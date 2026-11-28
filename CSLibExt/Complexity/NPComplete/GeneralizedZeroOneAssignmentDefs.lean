/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED 0-1 ASSIGNMENT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM GENERALIZED 0-1 ASSIGNMENT, citing S. Sahni and T. Gonzalez,
"P-complete approximation problems", Journal of the ACM 23(3) (1976), 555-565,
doi:10.1145/321958.321975;
S. Martello and P. Toth, *Knapsack Problems: Algorithms and Computer Implementations*, Wiley
(1990), Section 7.1, p. 190 (even the feasibility question of the generalized assignment problem
is NP-complete, by a reduction from PARTITION with two knapsacks).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment

/-- An instance: `m`, `n`, the matrix `A` (rows of `(positive part, negative part)` pairs), the
vector `b` (same encoding), the binary matrix `C` (rows of naturals), and the bound `K`. -/
abbrev GeneralizedZeroOneAssignmentInstance :=
  ℕ × ℕ × List (List (ℕ × ℕ)) × List (ℕ × ℕ) × List (List ℕ) × ℕ

/-- The integer encoded by a pair `(positive part, negative part)`. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- The entry `A_{r,c}`. -/
def entryA (i : GeneralizedZeroOneAssignmentInstance) (r : Fin i.1) (c : Fin i.2.1) : ℤ :=
  intOf ((i.2.2.1.getD r []).getD c (0, 0))

/-- The entry `b_r`. -/
def entryB (i : GeneralizedZeroOneAssignmentInstance) (r : Fin i.1) : ℤ :=
  intOf (i.2.2.2.1.getD r (0, 0))

/-- The entry `C_{r,c}`. -/
def entryC (i : GeneralizedZeroOneAssignmentInstance) (r : Fin i.1) (c : Fin i.2.1) : ℕ :=
  (i.2.2.2.2.1.getD r []).getD c 0

/-- Well-formedness of an instance: `A` and `C` have `m` rows of length `n`, `b` has length
`m`, every entry of `C` is `0` or `1`, and `K` is positive. -/
def WellFormed (i : GeneralizedZeroOneAssignmentInstance) : Prop :=
  i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.2.1) ∧
    i.2.2.2.1.length = i.1 ∧
    i.2.2.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.2.2.1, row.length = i.2.1 ∧ ∀ x ∈ row, x ≤ 1) ∧
    0 < i.2.2.2.2.2

/-- A binary matrix `X` with exactly one `1` in each column, satisfying `A X ≤ b` row by row,
with `∑ᵢ ∑ⱼ C_{i,j} X_{i,j} ≤ K`. -/
def GeneralizedZeroOneAssignmentFeasible (i : GeneralizedZeroOneAssignmentInstance) : Prop :=
  ∃ X : Fin i.1 → Fin i.2.1 → ℕ, (∀ r c, X r c ≤ 1) ∧ (∀ c, ∃! r, X r c = 1) ∧
    (∀ r, ∑ c, entryA i r c * (X r c : ℤ) ≤ entryB i r) ∧
    ∑ r, ∑ c, entryC i r c * X r c ≤ i.2.2.2.2.2

open Classical in
/-- GENERALIZED 0-1 ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def generalizedZeroOneAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedZeroOneAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedZeroOneAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment
