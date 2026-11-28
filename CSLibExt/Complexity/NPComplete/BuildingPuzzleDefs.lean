/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUILDING PUZZLE (SKYSCRAPERS): definitions

Source:
C. Iwamoto and Y. Matsui, "Computational complexity of building puzzles", IEICE Transactions
on Fundamentals of Electronics, Communications and Computer Sciences E99-A(6) (2016),
1145-1148, doi:10.1587/transfun.E99.A.1145;
problem statement as summarized in K. Haraguchi and R. Tanaka, "The building puzzle is still
hard even in the single lined version", Journal of Information Processing 25 (2017), 730-734,
doi:10.2197/ipsjjip.25.730.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import CSLibExt.Complexity.NPComplete.LatinSquareCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BuildingPuzzle



open LatinSquareCompletion

/-- An instance: the size `n` and the partial Latin square `S` (`0` = blank), and the Building
numbers `(top, bottom, left, right)` (`0` = none). -/
abbrev BuildingPuzzleInstance :=
  LatinSquareCompletionInstance × (List ℕ × List ℕ × List ℕ × List ℕ)

/-- The grid size `n`. -/
def size (i : BuildingPuzzleInstance) : ℕ := i.1.1

/-- The entry of `S` in row `r`, column `c` (`0` = blank). -/
def entry (i : BuildingPuzzleInstance) (r c : ℕ) : ℕ := (i.1.2.getD r []).getD c 0

/-- Well-formedness: `S` is an `n × n` grid with entries at most `n` and `n ≥ 1`, no nonzero
integer appears twice in a row or column of `S` (`0` is a blank and may repeat), and the four
lists of Building numbers have length `n` and entries at most `n`. -/
def WellFormed (i : BuildingPuzzleInstance) : Prop :=
  LatinSquareCompletion.WellFormed i.1 ∧
    (∀ r < size i, ∀ c < size i, ∀ c' < size i, c ≠ c' → entry i r c ≠ 0 →
      entry i r c ≠ entry i r c') ∧
    (∀ c < size i, ∀ r < size i, ∀ r' < size i, r ≠ r' → entry i r c ≠ 0 →
      entry i r c ≠ entry i r' c) ∧
    i.2.1.length = size i ∧ i.2.2.1.length = size i ∧ i.2.2.2.1.length = size i ∧
    i.2.2.2.2.length = size i ∧
    ∀ b ∈ i.2.1 ++ i.2.2.1 ++ i.2.2.2.1 ++ i.2.2.2.2, b ≤ size i

/-- The filled grid `h` (heights) satisfies the Building numbers: for each nonzero Building
number `b`, exactly `b` cells of its line are higher than every cell between them and the end
where `b` is written. -/
def BuildingCondition (i : BuildingPuzzleInstance) (h : Fin (size i) → Fin (size i) → ℕ) :
    Prop :=
  (∀ c : Fin (size i), i.2.1.getD c 0 ≠ 0 →
    (Finset.univ.filter fun r => ∀ r' < r, h r' c < h r c).card = i.2.1.getD c 0) ∧
  (∀ c : Fin (size i), i.2.2.1.getD c 0 ≠ 0 →
    (Finset.univ.filter fun r => ∀ r', r < r' → h r' c < h r c).card = i.2.2.1.getD c 0) ∧
  (∀ r : Fin (size i), i.2.2.2.1.getD r 0 ≠ 0 →
    (Finset.univ.filter fun c => ∀ c' < c, h r c' < h r c).card = i.2.2.2.1.getD r 0) ∧
  ∀ r : Fin (size i), i.2.2.2.2.getD r 0 ≠ 0 →
    (Finset.univ.filter fun c => ∀ c', c < c' → h r c' < h r c).card = i.2.2.2.2.getD r 0

/-- Some filling `h` with integers in `[n]` is a Latin square (no integer twice in a row or a
column), extends `S`, and satisfies the Building condition. -/
def BuildingPuzzleFeasible (i : BuildingPuzzleInstance) : Prop :=
  ∃ h : Fin (size i) → Fin (size i) → ℕ,
    (∀ r c, 1 ≤ h r c ∧ h r c ≤ size i) ∧
    (∀ r, Function.Injective (h r)) ∧
    (∀ c, Function.Injective fun r => h r c) ∧
    (∀ r c : Fin (size i), entry i r c = 0 ∨ entry i r c = h r c) ∧
    BuildingCondition i h

open Classical in
/-- BUILDING PUZZLE as a decision problem over bitstrings. -/
noncomputable def buildingPuzzleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BuildingPuzzleInstance) x with
  | some i => decide (WellFormed i ∧ BuildingPuzzleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BuildingPuzzle
