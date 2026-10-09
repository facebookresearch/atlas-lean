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

`lake build Verify` reads the front matter of every article under `roadmap/` and fails if a
name listed under `lean:` or `mathlib_declaration:` does not resolve to a declaration of this
build, with the namespaces opened below. The roadmap is the only list of the Mathlib results the
entry relies on, so a renamed or removed declaration, or a typo in an article, breaks the build;
there is no second, hand-maintained list to drift from it. The check also fails if it finds no
article or no name, so a moved roadmap cannot make it pass vacuously.
-/

open Lean Elab Command

/-- The comma-separated names listed under `key:` in the front matter of `text`. -/
def roadmapFrontmatterNames (key : String) (text : String) : List String := Id.run do
  let lines := text.splitOn "\n"
  unless lines.head? == some "---" do return []
  let mut names : List String := []
  for line in lines.drop 1 do
    if line == "---" then break
    if line.startsWith (key ++ ":") then
      let value := (line.drop (key.length + 1)).toString
      names := names ++ ((value.splitOn ",").map (·.trimAscii.toString)).filter (· ≠ "")
  return names

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
  let articles ← roadmapArticles roadmap
  let mut checked : Nat := 0
  let mut missing : Array String := #[]
  for article in articles do
    let text ← IO.FS.readFile article
    for key in ["lean", "mathlib_declaration"] do
      for name in roadmapFrontmatterNames key text do
        checked := checked + 1
        try
          discard <| liftTermElabM <| realizeGlobalConstNoOverload (mkIdent name.toName)
        catch _ =>
          missing := missing.push s!"{article.fileName.getD ""}: {key}: {name}"
  if articles.isEmpty || checked == 0 then
    throwError m!"roadmap check found {articles.size} articles and {checked} names"
  unless missing.isEmpty do
    throwError m!"roadmap names that do not resolve: {missing}"
  logInfo m!"{checked} roadmap names in {articles.size} articles resolve"

open MeasureTheory ProbabilityTheory Filter Topology in
#check_roadmap_names
