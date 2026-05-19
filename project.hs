{-# LANGUAGE DeriveFunctor #-}

import qualified Data.Set as S
import Data.Set (Set)
import Control.Category
import Prelude hiding ((.), id)

-- Wrapper type for memomory values needed to perform calculations with integers modulo 32
newtype MemVal = MemVal Int
  deriving (Eq, Ord, Show) 

-- Helper function for creating MemVals from integers
makeVal :: Int -> MemVal
makeVal n = MemVal (n `mod` 32)

-- Helper function for extracting integers from MemVals
getVal :: MemVal -> Int
getVal (MemVal n) = n

-- Creates a list of all possible memory values
allVals :: [MemVal]
allVals = map makeVal [0..31]

-- Alias for address values
type Addr = Int

-- Type representing intructions
data Instr =
  Mov Addr MemVal |
  Inc Addr |
  Dec Addr |
  Add Addr MemVal |
  Mul Addr MemVal |
  IfThenElse Pred Prog Prog |
  WhileDo Pred Prog
  deriving (Eq, Show)

-- Type representing category Prog
newtype Prog = Prog { getInstrs :: [Instr] }
  deriving (Eq, Show)

-- Helper functions for wrapping standalone intructions into programs
-- Needed to allow composability of instuctions via monoidal properties of Prog
skip :: Prog
skip = Prog []

mov :: Addr -> MemVal -> Prog
mov a v = Prog [Mov a v]

inc :: Addr -> Prog
inc a = Prog [Inc a]

dec :: Addr -> Prog
dec a = Prog [Dec a]

add :: Addr -> MemVal -> Prog
add a v = Prog [Add a v]

mul :: Addr -> MemVal -> Prog
mul a v = Prog [Mul a v]

ifThenElse :: Pred -> Prog -> Prog -> Prog
ifThenElse c p q = Prog [IfThenElse c p q]

whileDo :: Pred -> Prog -> Prog
whileDo c p = Prog [WhileDo c p]

-- Makes Prog a monoid as a category
instance Semigroup Prog where
  (<>) :: Prog -> Prog -> Prog
  (<>) (Prog xs) (Prog ys) = Prog (xs <> ys)

instance Monoid Prog where
  mempty :: Prog
  mempty  = skip
  mappend :: Prog -> Prog -> Prog
  mappend = (<>)

-- Type representing states
type State = [MemVal]

-- Type representing category Pred
type Pred  = Set State

-- A predicate corresponding to True (set of all possible states)
true :: Pred
true = S.fromList (statesOfLen 4)
  where
    statesOfLen 0 = [[]]
    statesOfLen k = [v:xs | v <- allVals, xs <- statesOfLen (k-1)]

-- A predicate corresponding to False (empty set)
false :: Pred
false = S.empty

-- Type representing category PT
newtype PT = PT { apply :: Pred -> Pred }

-- Makes PT a monoid as a category
instance Semigroup PT where
  (<>) :: PT -> PT -> PT
  PT f <> PT g = PT (f . g) 

instance Monoid PT where
  mempty :: PT
  mempty = PT id
  mappend :: PT -> PT -> PT
  mappend = (<>)

-- Helper function which updates a memory value at particular address
updateAt :: Addr -> (MemVal -> MemVal) -> State -> State
updateAt _ _ [] = []
updateAt 0 f (x:xs) = f x : xs
updateAt n f (x:xs) = x : updateAt (n - 1) f xs

-- Recursively finds least fixed point of a predicate transformer
lfp :: (Pred -> Pred) -> Pred
lfp f = go false
  where
    go x =
      let x' = f x
      in if x' == x then x else go x'

-- Converts a program to a corresponding predicate transformer by giving semantics to each instruction
wp :: Prog -> PT
wp (Prog instrs) = PT (\q -> foldr wpInstr q instrs)
  where
    wpInstr :: Instr -> Pred -> Pred
    wpInstr (Mov a v) q =
      S.filter (\s -> updateAt a (\_ -> v) s `S.member` q) true
    wpInstr (Inc a) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x + 1)) s `S.member` q) true
    wpInstr (Dec a) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x - 1)) s `S.member` q) true
    wpInstr (Add a v) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x + getVal v)) s `S.member` q) true
    wpInstr (Mul a v) q =
      S.filter (\s -> updateAt a (\x -> makeVal (getVal x * getVal v)) s `S.member` q) true
    wpInstr (IfThenElse c p r) q =
      predOr
        (predAnd c (apply (wp p) q))
        (predAnd (predNot c) (apply (wp r) q))
    wpInstr (WhileDo c p) q =
      lfp (\x ->
        predOr
          ((predNot c) `predAnd` q)
          (c `predAnd` (apply (wp p) x)))

-- Validates a Hoare triple
valid :: Pred -> Prog -> Pred -> Bool
valid precon prog postcon = precon `S.isSubsetOf` apply (wp prog) postcon

-- Predicate which checks if a value at particular address is equal to n
predEq :: Addr -> MemVal -> Pred
predEq addr (MemVal n) = S.filter (\s -> getVal (s !! addr) == n) true

-- Predicate which checks if a value at particular address is greater than n
predGr :: Addr -> MemVal -> Pred
predGr addr (MemVal n) = S.filter (\s -> getVal (s !! addr) > n) true

-- Predicate which checks if a value at particular address is greater or equal than n
predGrEq :: Addr -> MemVal -> Pred
predGrEq addr (MemVal n) = S.filter (\s -> getVal (s !! addr) >= n) true

-- Predicate which combines two other predicates using conjunction
predAnd :: Pred -> Pred -> Pred
predAnd p1 p2 = S.filter (\s -> s `S.member` p1 && s `S.member` p2) true

-- Predicate which combines two other predicates using disjunction
predOr :: Pred -> Pred -> Pred
predOr p q = S.filter (\s -> s `S.member` p || s `S.member` q) true

-- Negates a predicate
predNot :: Pred -> Pred
predNot p = S.filter (`S.notMember` p) true

-- Test validating Hoare triple {s[0] = 0} inc 0 {s[0] = 1}
test1 :: Bool
test1 = valid precon command postcon
  where
    command = inc 0
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 1)

-- Test validating Hoare triple {s[0] = 0 & s[1] = 0} inc 0; inc 0; inc 1; inc 1 {s[0] = 2 & s[1] = 2}
test2 :: Bool 
test2 = valid precon command postcon
  where
    command = inc 0 <> inc 0 <> inc 1 <> inc 1
    precon = predEq 0 (makeVal 0) `predAnd` predEq 1 (makeVal 0)
    postcon = predEq 0 (makeVal 2) `predAnd` predEq 1 (makeVal 2)

-- Test validating Hoare triple {True} mov 0,4; mul 0,4; mul 0,4 {s[0] = 0}
test3 :: Bool
test3 = valid precon command postcon
  where
    value = (makeVal 4)
    command = mov 0 value <> mul 0 value <> mul 0 value
    precon = true
    postcon = predEq 0 (makeVal 0)

-- Test validating Hoare triple {s[0] = 0} dec 0; add 0,10 {s[0] = 9}
test4 :: Bool
test4 = valid precon command postcon
  where
    command = dec 0 <> add 0 (makeVal 10)
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 10)

-- Test validating Hoare triple {s[0] = 0} skip; inc 0; skip {s[0] = 1}
test5 :: Bool
test5 = valid precon command postcon
  where
    command = skip <> inc 0 <> skip
    precon = predEq 0 (makeVal 0)
    postcon = predEq 0 (makeVal 1)

-- Test validating Hoare triple {s[0] = 5} if s[0] = 5 then mul 0,2 else skip {s[0] = 10}
test6 :: Bool
test6 = valid precon command postcon
  where
    command = ifThenElse (predEq 0 (makeVal 5)) (mul 0 (makeVal 2)) skip
    precon = predEq 0 (makeVal 5)
    postcon = predEq 0 (makeVal 10)

-- Test validating Hoare triple {s[0] = 4} while s[0] > 0 do dec 0 {s[0] = 0}
test7 :: Bool
test7 = valid precon command postcon
  where
    command = whileDo (predGr 0 (makeVal 0)) (dec 0)
    precon = predEq 0 (makeVal 4)
    postcon = predEq 0 (makeVal 0)

-- Test validating Hoare triple {s[0] = 4} while true do skip {s[0] = 0}
test8 :: Bool
test8 = valid precon command postcon
  where
    command = whileDo true skip
    precon = predEq 0 (makeVal 4)
    postcon = predEq 0 (makeVal 0)

main :: IO ()
main = putStrLn $ show test8