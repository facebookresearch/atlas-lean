/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THE HOUR-GLASS: definitions

Source:
H. Petersen, "The Complexity of Some Combinatorial Puzzles", arXiv:1507.08690 (2015), Theorem 2
("Generalized Hour-Glass is complete in NP").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HourGlass

/-- An instance: the width `m` of the first row, the rows of numbers (top to bottom, each left to
right), and the target sum `t`. -/
abbrev HourGlassInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: `0 < m`, there are `2m - 1` rows, and row `r` has width
`m - r` for `r < m` and `r + 2 - m` otherwise. -/
def WellFormed (i : HourGlassInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = 2 * i.1 - 1 ∧
    ∀ r < i.2.1.length,
      (i.2.1.getD r []).length = if r < i.1 then i.1 - r else r + 2 - i.1

/-- A path `p` (cell `p r` in row `r`) moving diagonally down from the first row to the last
row, whose numbers add up to `t`. -/
def HourGlassFeasible (i : HourGlassInstance) : Prop :=
  ∃ p : ℕ → ℕ, (∀ r < i.2.1.length, p r < (i.2.1.getD r []).length) ∧
    (∀ r, r + 1 < i.2.1.length →
      if r + 1 < i.1 then p (r + 1) + 1 = p r ∨ p (r + 1) = p r
      else p (r + 1) = p r ∨ p (r + 1) = p r + 1) ∧
    ∑ r ∈ Finset.range i.2.1.length, (i.2.1.getD r []).getD (p r) 0 = i.2.2

open Classical in
/-- THE HOUR-GLASS as a decision problem over bitstrings. -/
noncomputable def hourGlassDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HourGlassInstance) x with
  | some i => decide (WellFormed i ∧ HourGlassFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HourGlass
