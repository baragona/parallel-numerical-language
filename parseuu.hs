{-# LANGUAGE GADTs, ExistentialQuantification #-}

module Main where

import Text.ParserCombinators.UU
--import Data.Char
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.BasicInstances hiding (Parser)
--import System.IO
--import GHC.IO.Handle.Types
--import qualified Data.ListLike as LL

import Data.List


type Parser a = P (Str Char String LineColPos) a

data ShowBox where
  SB :: Show s => s -> ShowBox

run :: Show t =>  Parser t -> String -> IO ()
run p inp = do  let (a, errors) =  parse ( (,) <$> p <*> pEnd) (createStr (LineColPos 0 0 0) inp)
                putStrLn ("--  Result: " ++ show a)
                if null errors then  return ()
                               else  do putStr ("--  Correcting steps: \n")
                                        show_errors errors
                putStrLn "-- "
             where show_errors :: (Show a) => [a] -> IO ()
                   show_errors = sequence_ . (map (putStrLn . show))

allTheSame :: (Eq a) => [a] -> Bool
allTheSame xs = and $ map (== head xs) (tail xs)  
ambOK :: (Eq a) => Parser a -> Parser a
ambOK p =  (\results -> case (allTheSame results) of
                          True -> head results
                          False -> error "Not equal"
                    ) <$> amb p         

pConditional :: Parser a -> (a -> Bool) -> Parser a
pConditional p test = p >>= (\result -> case (test result) of
    True -> pure result
    False -> empty)

pChoices :: [Parser a] -> Parser a
pChoices list = foldr (<|>) empty list

myLexeme :: Parser a -> Parser a
myLexeme p = p <* pList_ng (pChoices (map pSym " \r\n\t"))

myParens :: Parser a -> Parser a
myParens p = (myLexeme (pSym '('  )) *> p <* (myLexeme (pSym ')'  ))

data Expression  =  NumberLiteralExpression Integer | IdentifierExpression String | ApplicationExpression Operator [Expression] | FunctionCallExpression Expression [Expression] 
    deriving (Show,Eq)

data Operator = Assign | Plus | Minus | Multiply | Divide | Power | HybridAssign Operator  deriving (Show,Eq)
--data Application = Application { operation :: Operator, arguments :: [Expression]} deriving (Show,Eq)
--data Assignment = Assignment {lvalue :: Expression, rvalue :: Expression} deriving (Show,Eq)

data NonemptyJoinedList ob j = NonemptyJoinedList ob (Maybe (j, NonemptyJoinedList ob j)) deriving (Eq)
nonemptyJoinedListObjectList :: (NonemptyJoinedList ob j) -> [ob]
nonemptyJoinedListObjectList (NonemptyJoinedList e (Just (_, le))) = [e] ++ nonemptyJoinedListObjectList le
nonemptyJoinedListObjectList (NonemptyJoinedList e (Nothing)) = [e]
nonemptyJoinedListJoinerList :: NonemptyJoinedList ob j -> [j]
nonemptyJoinedListJoinerList (NonemptyJoinedList _ (Just (o, le))) = [o] ++ nonemptyJoinedListJoinerList le
nonemptyJoinedListJoinerList (NonemptyJoinedList _ (Nothing)) = []
nonemptyJoinedListLength :: (NonemptyJoinedList ob j) -> Int
nonemptyJoinedListLength list = length (nonemptyJoinedListObjectList list)
concatNonemptyJoinedLists :: NonemptyJoinedList ob j -> j -> NonemptyJoinedList ob j -> NonemptyJoinedList ob j
concatNonemptyJoinedLists (NonemptyJoinedList e (Nothing)) op b = NonemptyJoinedList e (Just (op, b) )
concatNonemptyJoinedLists (NonemptyJoinedList e (Just (o, le))) op b = concatNonemptyJoinedLists (NonemptyJoinedList e (Nothing)) o (concatNonemptyJoinedLists le op b)
unitaryNonemptyJoinedList :: ob -> NonemptyJoinedList ob j
unitaryNonemptyJoinedList e = NonemptyJoinedList e (Nothing)
splitNonemptyJoinedListAt :: NonemptyJoinedList ob j -> Int -> (NonemptyJoinedList ob j, j, NonemptyJoinedList ob j)
splitNonemptyJoinedListAt (NonemptyJoinedList h (Just (o, le))) 1 = ( (unitaryNonemptyJoinedList h), o, le)
splitNonemptyJoinedListAt (NonemptyJoinedList _ (Nothing) ) _ = error "right side would be empty"
splitNonemptyJoinedListAt (NonemptyJoinedList h (Just (o, le))) idx = (concatNonemptyJoinedLists (unitaryNonemptyJoinedList h) o restLeft, splitOp, restRight)
    where
        (restLeft, splitOp, restRight) = splitNonemptyJoinedListAt le (idx - 1)
type UnassociatedExpression = NonemptyJoinedList Expression Operator

instance  (Show ob, Show j) => Show (NonemptyJoinedList ob j) where
    show x = concat  (zipWith (++) (map (\y -> "("++(show y)++")" ) (nonemptyJoinedListObjectList x))  ((map (\y -> "["++(show y)++"]" ) (nonemptyJoinedListJoinerList x))++[""])  )


data UnaryExpression = UnaryOp UnassociatedExpression

symbolForOperator :: Operator -> String
symbolForOperator op = case op of
    Assign -> "="
    Plus -> "+" 
    Minus -> "-"
    Multiply -> "*"
    Divide -> "/"
    Power -> "^"
    HybridAssign o-> (symbolForOperator o)++"="
    
data Associativity = LeftAssociative | RightAssociative  deriving (Show,Eq)

hybridAssignments :: [Operator]
hybridAssignments = map HybridAssign [Plus,Minus,Multiply,Divide,Power]

operatorPrecedenceGroups :: [([Operator],Associativity)]
operatorPrecedenceGroups       = [
  (Assign:hybridAssignments, RightAssociative),
  ([Plus, Minus], LeftAssociative),
  ([Multiply,Divide], LeftAssociative),
  ([Power], RightAssociative)
  ]

allOperators :: [Operator]
allOperators = hybridAssignments++[Assign]++[Plus,Minus,Multiply,Divide,Power]

pOperator :: Parser Operator
pOperator = pChoices (map (\c -> c <$ myLexeme (pToken (symbolForOperator c)) ) allOperators)

pCallable :: Parser Expression
pCallable = (IdentifierExpression <$> pIdentifier) <|> myParens pExpression

pFunctionCall :: Parser Expression
pFunctionCall =
     (
     ((\fname args -> FunctionCallExpression fname args ) <$> pCallable) <*>
       (
       -- ( (pSym ' ') *> ((\x -> [x]) <$> pExpression) ) <|> -- no parens call - single argument only - but a single parenthesized argument is also handled here
       micro ( myParens ( (pListSep_ng pComma (pExpression))) ) 1 -- parens call, need at least 2 arguments
       )
    )
pOperatorAssignment :: Parser Operator -- parses things like +=, *= etc
pOperatorAssignment = myLexeme (
        (
          pChoices [  op <$ (pToken (symbolForOperator op)) | op <- hybridAssignments]
        ) <* (pSym '=')
    )
       
pLvalue :: Parser Expression
pLvalue = (IdentifierExpression <$> pIdentifier) <|> myParens pExpression



myInteger :: Parser Integer
myInteger = pInteger

pIdentifier :: Parser String
pIdentifier =  (myLexeme (( (\x y -> [x]++y) <$> pLetter) <*> (pList_ng (pLetter <|> pDigit))))



pCompoundExpression :: Parser UnassociatedExpression

pCompoundExpression = (unitaryNonemptyJoinedList <$> pExpressionPiece) <|>
     (((\x y z -> concatNonemptyJoinedLists (unitaryNonemptyJoinedList x) y z ) <$> pExpressionPiece)
         <*> pOperator <*> pCompoundExpression)

pThingyList :: Parser [Either Operator Expression]

pThingyList = pList_ng (Left <$> pOperator <|> Right <$> pExpressionPiece)

haveSomethingInCommon :: Eq a => [a] -> [a] -> Bool
haveSomethingInCommon x y = any (\el -> elem el y) x

surely :: Maybe a -> a
surely (Just a) = a
surely Nothing = error "Surely you're joking?"

findLastIndex :: (a -> Bool) -> [a] -> Maybe Int
findLastIndex test list = case (findIndex test (reverse list) ) of 
    Nothing -> Nothing
    Just idx -> Just ( (length list) - idx - 1)

associateExpression :: UnassociatedExpression -> Expression
associateExpression ue = 
    case ue of
        NonemptyJoinedList e Nothing -> e
        NonemptyJoinedList _ _ -> ApplicationExpression splitOp [associateExpression splitLeft, associateExpression splitRight]
            where
                -- highestToLowest = reverse operatorPrecedenceGroups
                operatorList :: [Operator]
                operatorList = (nonemptyJoinedListJoinerList ue)
                groupMatches :: ([Operator], Associativity) -> Bool
                groupMatches (ops, _) = haveSomethingInCommon operatorList ops
                matchingGroup :: ([Operator], Associativity)
                matchingGroup = surely (find (\g -> groupMatches g) operatorPrecedenceGroups)
                matchingOpIndex :: Int
                matchingOpIndex = case matchingGroup of 
                    (ops, LeftAssociative) -> surely (findLastIndex (\op -> elem op ops) operatorList)
                    (ops, RightAssociative) -> surely (findIndex (\op -> elem op ops) operatorList)
                (splitLeft, splitOp, splitRight) = splitNonemptyJoinedListAt ue (matchingOpIndex + 1)
        


pExpressionPiece :: Parser Expression
pExpressionPiece = pChoices [
                                                (IdentifierExpression <$> pIdentifier),
                                                (NumberLiteralExpression <$> myInteger),
                                                myParens pExpression,
                                                micro ( pFunctionCall) 1
                                                -- micro (AssignmentExpression <$> pAssignment) 1
                                                ]

pExpression :: Parser Expression

pExpression = associateExpression <$> pCompoundExpression
