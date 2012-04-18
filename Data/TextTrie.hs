{-# LANGUAGE OverloadedStrings, PatternGuards #-}

module Data.TextTrie
( Trie ()
, size
, fromList
, fromLang
, lookup
, insert
) where

import Prelude hiding (lookup)
import Data.Bits (testBit, xor, bitSize)
import Data.Maybe (fromJust)
import Data.List (findIndex, foldl')
import Control.Monad (guard)
import qualified Data.Text as T

{-
Text Patricia Trie datatype.

Invariants: 
1. Arc key is not empty (no way to represent empty key in such a trie)
2. Not (empty Arc value `and` empty subtrie)
3. Branch subtrie is non-empty.
4. First (k-1) bits in first characters in both subtries of a branch
   are the same, where k is a position of a branching bit (BrBit)
5. If (Maybe a) is Nothing, then Arc subtrie is a Branch

We represent invariants 1, 2 and 3 by means of smart data constructors.
TODO: Other invariants are tested using QuickCheck.

TODO: A common bit prefix (see invariant 3) could be stored in a
trie branch. It would make insertion operations faster, but the
structure itself would have bigger memory footprint (how much bigger?).

TODO: Is it possible to replace invariant 1 with:
1'. Key non-empty, unless Arc is absolute root of tree

TODO: Change findDiffBit and match functions to get Big-endian version.
-}

-- | Branching Bit.
type BrBit  = Int -- Word8

-- The order of constructors of Trie matters when considering performance
-- (see Data.IntMap implementation for more information).
data Trie a
    = Branch {-# UNPACK #-} !BrBit
             !(Trie a)
             !(Trie a)
    | Arc    {-# UNPACK #-} !T.Text
             !(Maybe a)
             !(Trie a)
    | Empty

instance Show a => Show (Trie a) where
    show Empty = "ϵ"
    show (Arc k mv t) =
        let ts = unlines $ map ("  "++) $ lines $ show t
        in  "Arc " ++ show k ++ " " ++ show mv ++ "\n" ++ ts
    show (Branch b l r) =
        let ls = unlines $ map ("  "++) $ lines $ show l
            rs = unlines $ map ("  "++) $ lines $ show r
        in  "[L] Branch " ++ show b ++ "\n" ++ ls ++
            "[R] Branch " ++ show b ++ "\n" ++ rs

size :: Trie a -> Int
size Empty = 0
size (Arc _ Nothing t) = size t
size (Arc _ (Just _) t) = size t + 1
size (Branch _ l r) = size l + size r

size' :: Trie a -> (Int, Int, Int)
size' x = case x of
    Empty           -> (0, 0, 1)
    (Arc _ _ t)     -> size' t .+. (0, 1, 0)
    (Branch _ l r)  -> size' l .+. size' r .+. (1, 0, 0)
  where
    (.+.) (x, y, z) (x', y', z') = (x+x', y+y', z+z')

-- | Prune arcs that lead nowhere.
mkArc :: T.Text -> Maybe a -> Trie a -> Trie a
mkArc ""  mv t
    | Just _ <- mv = error "mkArc: Empty key with Just value"
    | otherwise    = t
mkArc k Nothing Empty = Empty 
mkArc k Nothing (Arc k' mv' t') = Arc (T.append k k') mv' t'
mkArc k mv t = Arc k mv t
{-# INLINE mkArc #-}

mkBranch :: BrBit -> Trie a -> Trie a -> Trie a
mkBranch _ Empty r = r  
mkBranch _ l Empty = l  
mkBranch b l r     = Branch b l r
{-# INLINE mkBranch #-}

lookup :: T.Text -> Trie a -> Maybe a
lookup _ Empty = Nothing
lookup k (Arc k' mv t) = do
    suf <- T.stripPrefix k' k
    if T.null suf
        then mv
        else lookup suf t
-- | TODO: Check Data.Char.ord function instead of fromEnum.
lookup k branch@(Branch _ _ _) =
    let code = fromEnum $ T.head k
    in  brLookup code k branch
    
-- | Branch lookup.
brLookup :: Int -> T.Text -> Trie a -> Maybe a
brLookup code k (Branch brBit leftTrie rightTrie) =
    if testBit code brBit
        then brLookup code k rightTrie
        else brLookup code k leftTrie
brLookup _ k t = lookup k t

-- | Merging two tries.  TODO: Make it work for branches.
merge :: Trie a -> Trie a -> Trie a
merge Empty t = t
merge t Empty = t
merge arc@(Arc k mv t) arc'@(Arc k' mv' t')
    | k == k' =
        mkArc k mv' $ merge t t'    -- ^ Taking value from right arc
    | Nothing <- T.commonPrefixes k k' =
        let code  = fromEnum $ T.head k
            code' = fromEnum $ T.head k'
            brBit = findDiffBit code code'
        in  if testBit code brBit
                then mkBranch brBit arc' arc
                else mkBranch brBit arc arc'
    | Just (pref, "", suf')  <- T.commonPrefixes k k' =
        mkArc k mv $ merge t (mkArc suf' mv' t')
    | Just (pref, suf, "")   <- T.commonPrefixes k k' =
        mkArc k' mv' $ merge (mkArc suf mv t) t'
    | Just (pref, suf, suf') <- T.commonPrefixes k k' =
        mkArc pref Nothing $ merge (mkArc suf mv t) (mkArc suf' mv' t')
merge arc@(Arc k (Just x) Empty) br@Branch{} = insert k x br
merge br@Branch{} arc@(Arc k (Just x) Empty) = insert k x br

insert :: T.Text -> a -> Trie a -> Trie a
insert k x Empty = mkArc k (Just x) Empty
insert k x arc@Arc{} = merge arc $ mkArc k (Just x) Empty
insert k x br@(Branch brBit leftTrie rightTrie)
    | match code code' (brBit-1) =
        if testBit code brBit
            then mkBranch brBit leftTrie (insert k x rightTrie)
            else mkBranch brBit (insert k x leftTrie) rightTrie
    | otherwise =
        if testBit code brBit'
            then mkBranch brBit' br arc
            else mkBranch brBit' arc br
  where
    code   = fromEnum $ T.head k
    code'  = fromEnum $ T.head $ findFirstKey leftTrie
    brBit' = findDiffBit code code'
    arc    = mkArc k (Just x) Empty

fromList :: [(T.Text, a)] -> Trie a
fromList =
    let update t (k, v) = insert k v t
    in  foldl' update Empty

fromLang :: [T.Text] -> Trie ()
fromLang xs = fromList [(x, ()) | x <- xs]

-- | Find first different bit.
findDiffBit :: Int -> Int -> Int
findDiffBit x y =
    let bits x = [testBit x k | k <- [0 .. (bitSize x) - 1]]
    in  fromJust $ findIndex (True==) $ bits $ x `xor` y

-- | Check if x and y match on first k-1 bits.
match :: Int -> Int -> Int -> Bool
match x y k =
    and [testBit x i == testBit y i | i <- [0..k-1]]

-- | Find first Arc key in a branch subtries.
findFirstKey :: Trie a -> T.Text
findFirstKey (Branch _ l _) = findFirstKey l
findFirstKey (Arc k _ _) = k
findFirstKey Empty = error "findFirstKey: invariant 3 broken"
