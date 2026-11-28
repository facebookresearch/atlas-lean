/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTANGLE TILING: definitions

Source:
S. Khanna, S. Muthukrishnan and M. Paterson, "On approximating rectangle tiling and packing",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 384-393
(Section 1.1, problem RTILE; Theorem 2.1: RTILE is NP-hard even with element weights that are
non-negative integers bounded by a constant, by a reduction from PLANAR-3SAT); research report
version: Department of Computer Science Research Report CS-RR-339, University of Warwick (1998);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MINIMUM
RECTANGLE TILING.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectangleTiling

/-- An instance: the rows of the array `A`, the number `p` of rectangles and the weight bound
`K`. -/
abbrev RectangleTilingInstance := List (List ℕ) × ℕ × ℕ

/-- The side `n` of the array: its number of rows. -/
abbrev side (i : RectangleTilingInstance) : ℕ := i.1.length

/-- The element `A[r][c]` of the array. -/
def entry (i : RectangleTilingInstance) (x : Fin (side i) × Fin (side i)) : ℕ :=
  (i.1.getD x.1 []).getD x.2 0

/-- Well-formedness of an instance: the array is square (every row has `n` elements), and `p`
and `K` are positive. -/
def WellFormed (i : RectangleTilingInstance) : Prop :=
  (∀ row ∈ i.1, row.length = side i) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some partition of the cells into at most `p` rectangles gives every rectangle weight at most
`K`. -/
def RectangleTilingFeasible (i : RectangleTilingInstance) : Prop :=
  ∃ g : Fin (side i) × Fin (side i) → Fin i.2.1,
    (∀ j, ∃ r₁ r₂ c₁ c₂ : ℕ, ∀ x,
      g x = j ↔ (r₁ ≤ x.1 ∧ (x.1 : ℕ) ≤ r₂ ∧ c₁ ≤ x.2 ∧ (x.2 : ℕ) ≤ c₂)) ∧
    ∀ j, (∑ x ∈ Finset.univ.filter (fun x => g x = j), entry i x) ≤ i.2.2

open Classical in
/-- RECTANGLE TILING as a decision problem over bitstrings. -/
noncomputable def rectangleTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectangleTilingInstance) x with
  | some i => decide (WellFormed i ∧ RectangleTilingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RectangleTiling
