/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib
import Code

/-!
# Roadmap names

`lake build Verify` reads the front matter of every Markdown file under `roadmap/` and fails if
a name listed under `lean:` or `mathlib_declaration:` does not resolve to a declaration of this
build, with the namespaces opened below, or if a front matter block cannot be read. The
roadmap is the only list of the Mathlib results the entry relies on, so a renamed or removed
declaration, or a typo in an article, breaks the build; there is no second, hand-maintained list
to drift from it. The check also fails if it finds no
article or no name, so a moved roadmap cannot make it pass vacuously.
-/

open Lean Elab Command

/-- The `key: value` entries of the front matter of `text`, read as autoform reads them: the
block opens on the first line, lines are trimmed (so CRLF line endings are fine), blank and `#`
lines are skipped. Anything else, such as a YAML block list or a block that does not start on
the first line, is an error rather than a silent skip. -/
def roadmapFrontmatter (text : String) : Except String (List (String × String)) := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  match lines with
  | [] => return []
  | first :: rest =>
    if first != "---" then
      if lines.any (· == "---") && (lines.takeWhile (· == "")).length > 0 then
        throw "front matter must start on the first line"
      return []
    let mut entries : List (String × String) := []
    let mut closed := false
    for line in rest do
      if line == "---" then
        closed := true
        break
      if line == "" || line.startsWith "#" then continue
      match line.splitOn ":" with
      | key :: value :: more =>
        let value := (":".intercalate (value :: more)).trimAscii.toString
        if value == "" then throw s!"`{key}:` has no value; list names on one line"
        entries := entries ++ [(key.trimAscii.toString, value)]
      | _ => throw s!"expected `key: value` in front matter, found `{line}`"
    unless closed do throw "unterminated front matter"
    return entries

/-- The comma-separated names listed under `key` in front matter `entries`. -/
def roadmapNames (key : String) (entries : List (String × String)) : List String :=
  (entries.filter (·.1 == key)).flatMap fun (_, value) ↦
    ((value.splitOn ",").map (·.trimAscii.toString)).filter (· ≠ "")

/-- The Markdown files below `dir`. -/
partial def roadmapArticles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut found := #[]
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      found := found ++ (← roadmapArticles entry.path)
    else if entry.path.extension == some "md" then
      found := found.push entry.path
  return found

open MeasureTheory ProbabilityTheory Filter Topology in
/-- Check that every `lean:` and `mathlib_declaration:` name of the roadmap resolves. -/
elab "#check_roadmap_names" : command => do
  let some verifyDir := (System.FilePath.mk (← getFileName)).parent
    | throwError "cannot locate this file"
  let some entryDir := verifyDir.parent | throwError "cannot locate the entry directory"
  let roadmap := entryDir / "roadmap"
  unless ← roadmap.isDir do
    throwError m!"roadmap directory not found: {roadmap}"
  let files ← roadmapArticles roadmap
  let mut articles : Nat := 0
  let mut checked : Nat := 0
  let mut missing : Array String := #[]
  let mut unreadable : Array String := #[]
  for file in files do
    let label := (file.toString.drop (roadmap.toString.length + 1)).toString
    match roadmapFrontmatter (← IO.FS.readFile file) with
    | .error e => unreadable := unreadable.push s!"{label}: {e}"
    | .ok entries =>
      -- statement articles carry `declaration:`; the other files are container pages
      if entries.any (·.1 == "declaration") then articles := articles + 1
      for key in ["lean", "mathlib_declaration"] do
        for name in roadmapNames key entries do
          checked := checked + 1
          try
            discard <| liftTermElabM <| realizeGlobalConstNoOverload (mkIdent name.toName)
          catch _ =>
            missing := missing.push s!"{label}: {key}: {name}"
  unless unreadable.isEmpty do
    throwError m!"roadmap front matter that cannot be read: {unreadable}"
  if articles == 0 || checked == 0 then
    throwError m!"roadmap check found {articles} articles and {checked} names"
  unless missing.isEmpty do
    throwError m!"roadmap names that do not resolve: {missing}"
  logInfo m!"{checked} roadmap names in {articles} articles resolve \
    ({files.size - articles} container pages read too)"

open MeasureTheory ProbabilityTheory Filter Topology in
#check_roadmap_names
