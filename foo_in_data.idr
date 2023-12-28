module Main

isValid : (name : String) -> Bool
isValid name = if name == "BAD_NAME" then False else True

data VerFile : Type where
    MkVerFile : (name : String) -> isValid name = True -> VerFile

example1 = MkVerFile "GOOD_NAME" Refl
-- This won't compile because "BAD_NAME" is not valid according to isValid
example2 = MkVerFile "BAD_NAME" Refl
