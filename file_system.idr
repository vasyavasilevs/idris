module Main


import Data.String

--%default total

{-
data PERMISSIONS = READ | WRITE | EXECUTE
data 

data NewFileName : String -> Type where
    NonTheSame : 

data NotJopa : String -> Type where
  IsNotJopa : (name : String) -> NotJopa name
    
data File : Type where
    InitFile : File INIT_EXE
    MkFile : File ((\name => if name == "Jopa" then impossible else name) : String)


data UniqueName : (name : String) -> Type where
    MkUniqueName : \name => case name of 
                                        ?unique => True

-}   

{- 

data File : Type -> Type where
  INIT_EXE : File a
  OrdinaryFile : a -> File a

data Folder : Type -> Type where
  ROOT : Folder a
  Directory : File a -> Folder a

data FILES : Type -> Type where
  Files : List (File a) -> FILES a
  Folders : List (Folder a) -> FILES a

data PERMISSIONS = READ | WRITE | EXECUTE

data State = Readable | Writeable | Executable

statePermissions : State -> List PERMISSIONS
statePermissions Readable = [READ]
statePermissions Writeable = [WRITE]
statePermissions Executable = [EXECUTE]

-- Пример файловой системы
main : IO ()
main = do
  let executableFile : File String
      executableFile = INIT_EXE

  let textFile : File String
      textFile = OrdinaryFile "Hello, World!"

  let rootFolder : Folder String
      rootFolder = ROOT

  let folderWithFile : Folder String
      folderWithFile = Directory textFile

  let filesSystem : FILES String
      filesSystem = Files [executableFile, textFile]

  let foldersSystem : FILES String
      foldersSystem = Folders [rootFolder, folderWithFile]

  putStrLn $ show filesSystem
  putStrLn $ show foldersSystem



--data File' : (name : String) -> (existNames : List String) -> Type

{- 

data File : Type where
    File' : (name : String) -> (parent : Folder) -> File
    Folder : (name : String) -> (parent : Folder) -> File 

sampleFile
-}


{- 
data FILES : (name : String) -> (parent : FILES) -> Type where
    InitFile : "INIT_EXE" -> 
-}

{- 

FILES : Type
FILES = List Files

data Files = File | Folder
data File obj = INIT_EXE | OrdinaryFile obj

data FileSystem : Type where
    InitSystem :  
-}

{- 
ListOfNames : List String
ListOfNames = ["INIT_EXE"]
    
data NaiveFile : Type where
    MkFile : (name : String) -> NaiveFile

data VerifiedName : Type where
    MkVerFile : MkFile-> VerifiedName

exampleFile = MkFile "INIT_EXE"
exampleVerifiedName1 = MkVerFile "OTHER_NAME" Refl
exampleVerifiedName2 = MkVerFile "INIT_EXE" Refl
-}

{-


ListOfNames : List String
ListOfNames = ["INIT_EXE"]
    
data NaiveFile : Type where
    MkFile : (name : String) -> NaiveFile

data VerifiedName : (name : String) -> (Type -> Bool) -> Type where
    MkVerFile : (name : String) 
                -> (name == (head ListOfNames) = False) 
                -> VerifiedName name (\file => True)

exampleFile = MkFile "INIT_EXE"
exampleVerifiedName1 = MkVerFile "OTHER_NAME" Refl
exampleVerifiedName2 = MkVerFile "INIT_EXE" Refl


ListOfNames : List String
ListOfNames = ["INIT_EXE"]
    
data NaiveFile : Type where
    MkFile : (name : String) -> NaiveFile

data VerifiedName : (NaiveFile String) -> (name -> Bool) -> Type where
    MkVerFile : (name == (head ListOfNames) = False) -> VerifiedName name (\file => True)

exampleFile = MkFile "INIT_EXE"
exampleVerifiedName1 = MkVerFile "OTHER_NAME" Refl
exampleVerifiedName2 = MkVerFile "INIT_EXE" Refl


data File obj = INIT_EXE | OrdinaryFile obj
data Folder obj = ROOT | Directory (File obj)
data FILES obj = Files (List File obj) | Folders (List Folder obj) 
data PERMISSIONS = READ | WRITE | EXECUTE
data State = Readable | Writeable | Executable

(state : State -> List PERMISSIONS)



{-
 
data FileSystem : ((typeOfObj : Type) -> FILES typeOfObj) -> Type where
    MkInit : (\init => case init of
                                INIT_EXE => Files INIT_EXE
                                OrdinaryFile init => impossible)

data FileSystem : ((typeOfObj : Type) -> FILES typeOfObj) -> Type where
    MkInit : (init : Type) -> FileSystem (\typeOfObj => case init of
                                                            INIT_EXE => Files INIT_EXE
                                                            OrdinaryFile obj => Folders (Directory (OrdinaryFile obj)))



-- Invariant: Set of files is limited
FilesLimited : FileSystem -> Type
FilesLimited (MkFileSystem files _ _ _ _) = length files <= MAX_FILES


-- Invariant: Each folder has at most one parent
FileParentsUnique : FileSystem -> Type
FileParentsUnique (MkFileSystem _ _ fileParents _ _) =
  (allUnique (map fst fileParents)) where 
      -- Helper function to check if all elements in a list are unique
    allUnique : Eq a => List a -> Bool
    allUnique [] = True
    allUnique (x :: xs) = not (x `elem` xs) && allUnique xs

-- Invariant: Each folder has at least one parent (except ROOT)
FolderParents : FileSystem -> Type
FolderParents (FileSystem files folders fileParents _ _) =
  (all (\(_, parent) => parent /= "") fileParents) && all (\f => f /= ROOT) folders && all (\f => f `elem` files) folders

-- Initialization: Set initial values for the file system
initFileSystem : FileSystem
initFileSystem = FileSystem [ ROOT, INIT_EXE ] [ ROOT ] [ (INIT_EXE, "ROOT") ] [ (ROOT, [READ, WRITE, EXECUTE]), (INIT_EXE, [READ, EXECUTE]) ] [ (ROOT, []), (INIT_EXE, [ ROOT ]) ]


-}


-}
-}

foo : String -> Bool
foo str = if str == "hello" then True else False 

data MyData : (String -> Bool) -> Type where 
    MkData : MyData foo 