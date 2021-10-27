module Solver.Backtracking (solution) where

import CNF
import CNF.Eval

import Data.List
import Data.Maybe

test = [BigOr [Lit 1 True, Lit 2 False], BigOr [Lit 2 True, Lit 3 True],
        BigOr [Lit 1 False, Lit 3 False], 
        BigOr [Lit 1 False, Lit 2 False, Lit 3 True]]

test2 = [ BigOr [ Lit 1 True, Lit 1 False ] ]

test3 = [ BigOr [Lit 3 False] , BigOr [Lit 3 True]]

test4 = [ BigOr [Lit 1 True , Lit 2 True] , BigOr [Lit 1 False , Lit 2 False]]

fstL :: Lit -> Var
fstL (Lit var pol) = var

sndL :: Lit -> Bool
sndL (Lit var pol) = pol

varsCls :: Cls -> [Var]
varsCls (BigOr c) = (foldr (\x acc -> if (fstL x `elem` acc) then acc else (fstL x) : acc) ([])) c

varsFrm :: [Cls] -> [Var]
varsFrm f = (foldr (\x acc -> nub ((varsCls x) ++ acc)) ([])) f

giveSub :: [Var] -> Subst
giveSub [] = []
giveSub (x : xs) = [(x , True)] ++ giveSub(xs)

var_in_cls :: Lit -> [Lit] -> Cls -> Maybe Cls
var_in_cls v now (BigOr []) = Just (BigOr now)
var_in_cls v now (BigOr (x : xs)) = case (fst (unLit x) == fst (unLit v)) of
                                      True -> case ((snd (unLit x)) == snd (unLit v)) of
                                                True -> Nothing
                                                False -> var_in_cls v now (BigOr xs)
                                      False -> var_in_cls v (now ++ [x]) (BigOr xs)

condition :: Lit -> [Cls] -> Maybe [Cls]
condition v [] = Nothing
condition v (x : xs) = case (var_in_cls v [] x) of
                         Nothing -> condition v xs
                         Just k -> case null (literals k) of
                                     True -> Just []
                                     False -> case condition v xs of
                                                Nothing -> Just [k]
                                                Just ks -> case ks of
                                                             [] -> Just []
                                                             z : zs -> Just ([k] ++ (z : zs))

findVariable :: Cls -> Maybe Var
findVariable (BigOr f) = case f of
                           [] -> Nothing
                           x : xs -> Just (var x)

findSingleLit :: [Cls] -> Maybe Lit
findSingleLit [] = Nothing
findSingleLit (y : ys) = case (length (literals y)) of
                           1 -> Just ((literals y)!!0)
                           otherwise -> findSingleLit ys

solve :: [Cls] -> Subst -> Maybe Subst
solve [] s = Just []
solve (x : xs) s = case findSingleLit (x : xs) of
                     Nothing -> case findVariable x of
                                  Nothing -> Nothing
                                  Just v -> case (condition (Lit v True) (x : xs)) of
                                              Nothing -> Just (s ++ [(v , True)])
                                              Just k -> case k of
                                                          [] -> case (condition (Lit v False) (x : xs)) of
                                                                  Nothing -> Just (s ++ [(v , False)])
                                                                  Just k -> case k of
                                                                              [] -> Nothing
                                                                              y : ys -> solve (y : ys) (s ++ [(v , False)])
                                                          y : ys -> case (solve (y : ys) (s ++ [(v , True)])) of
                                                                      Nothing -> case (condition (Lit v False) (x : xs)) of
                                                                                   Nothing -> Just (s ++ [(v , False)])
                                                                                   Just k -> case k of
                                                                                               [] -> Nothing
                                                                                               z : zs -> solve (z : zs) (s ++ [(v , False)])
                                                                      Just s -> Just s
                     Just v -> case (condition (v) (x : xs)) of
                                Nothing -> Just (s ++ [(var v , pol v)])
                                Just k -> case k of
                                            [] -> Nothing
                                            y : ys -> solve (y : ys) (s ++ [(var v , pol v)])

getVarFromSubst :: Subst -> [Var]
getVarFromSubst [] = []
getVarFromSubst (x : xs) = [fst x] ++ (getVarFromSubst xs)

solution :: CNF -> Maybe Subst
solution f = case (solve fc []) of
                Nothing -> Nothing
                Just s -> Just (s ++ (giveSub ((vars f) \\ (getVarFromSubst s))))
    where
        fc = clauses f