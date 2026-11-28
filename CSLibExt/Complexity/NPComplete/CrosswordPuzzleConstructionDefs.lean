/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CROSSWORD PUZZLE CONSTRUCTION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GP14] CROSSWORD PUZZLE
CONSTRUCTION (credited there to Lewis and Papadimitriou);
J. Engel, M. Holzer, O. Ruepp, and F. Sehnke, "On computer integrated rationalized
crossword puzzle manufacturing", Fun with Algorithms (FUN 2012), Lecture Notes in
Computer Science 7288 (2012), 131-141, doi:10.1007/978-3-642-30347-0_15 (records the
attribution).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction

/-- An instance: the word list `W` (letters are natural numbers), the side length `n`, and
the matrix `A` as a list of rows, with `true` for a `1` and `false` for a `0`. -/
abbrev CrosswordPuzzleConstructionInstance := List (List ℕ) × ℕ × List (List Bool)

/-- Well-formedness of an instance: `W` lists distinct words, and `A` has `n` rows of length
`n`. -/
def WellFormed (i : CrosswordPuzzleConstructionInstance) : Prop :=
  i.1.Nodup ∧ i.2.2.length = i.2.1 ∧ ∀ row ∈ i.2.2, row.length = i.2.1

/-- Square `(r, c)` (row `r`, column `c`) is in `E`, a square to be filled with a letter: it
lies in the matrix and its entry is `0`. Squares outside the matrix count as `1`'s (blank
squares of the puzzle), so they end runs at the border. -/
def Fillable (i : CrosswordPuzzleConstructionInstance) (r c : ℕ) : Prop :=
  (i.2.2.getD r []).getD c true = false

/-- A filling `f` of the squares such that every maximal horizontal run of squares of `E`
(row `r`, columns `a, ..., b - 1`) and every maximal vertical run (column `c`, rows
`a, ..., b - 1`) spells, in order, a word of `W`. -/
def CrosswordPuzzleConstructionFeasible (i : CrosswordPuzzleConstructionInstance) : Prop :=
  ∃ f : ℕ → ℕ → ℕ,
    (∀ r a b, a < b → (∀ c, a ≤ c → c < b → Fillable i r c) →
      (a = 0 ∨ ¬ Fillable i r (a - 1)) → ¬ Fillable i r b →
        (List.range' a (b - a)).map (fun c => f r c) ∈ i.1) ∧
    (∀ c a b, a < b → (∀ r, a ≤ r → r < b → Fillable i r c) →
      (a = 0 ∨ ¬ Fillable i (a - 1) c) → ¬ Fillable i b c →
        (List.range' a (b - a)).map (fun r => f r c) ∈ i.1)

open Classical in
/-- CROSSWORD PUZZLE CONSTRUCTION as a decision problem over bitstrings. -/
noncomputable def crosswordPuzzleConstructionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CrosswordPuzzleConstructionInstance) x with
  | some i => decide (WellFormed i ∧ CrosswordPuzzleConstructionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CrosswordPuzzleConstruction
