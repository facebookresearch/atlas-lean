/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3-INDEX ASSIGNMENT: definitions

Source:
A. M. Frieze, "Complexity of a 3-dimensional assignment problem", European Journal of
Operational Research 13 (1983), 161-164, doi:10.1016/0377-2217(83)90078-4;
A. Ćustić, B. Klinz and G. J. Woeginger, "Planar 3-dimensional assignment problems with
Monge-like cost arrays", arXiv:1405.5210 (2014), Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeIndexAssignment

/-- An instance: the size `n`, the cost array as a list of `n³` integers, the cost `c_{ijk}`
at position `(i * n + j) * n + k`, and the bound `B`. Each integer is a pair `(p, q)` of
natural numbers standing for `p - q`. -/
abbrev PlanarThreeIndexAssignmentInstance := ℕ × List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: `n ≥ 1` and the cost list has exactly `n³` entries. -/
def WellFormed (i : PlanarThreeIndexAssignmentInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ^ 3

/-- The cost `c_{ijk}` as an integer. -/
def cost (i : PlanarThreeIndexAssignmentInstance) (a b c : Fin i.1) : ℤ :=
  let e := i.2.1.getD ((a.val * i.1 + b.val) * i.1 + c.val) (0, 0)
  (e.1 : ℤ) - e.2

/-- There is a Latin square `L`, i.e. every row `L a` and every column `fun a => L a b` is
injective, whose cells `(a, b, L a b)` have total cost at most `B`. -/
def PlanarThreeIndexAssignmentFeasible (i : PlanarThreeIndexAssignmentInstance) : Prop :=
  ∃ L : Fin i.1 → Fin i.1 → Fin i.1,
    (∀ a, Function.Injective (L a)) ∧ (∀ b, Function.Injective (fun a => L a b)) ∧
      ∑ a, ∑ b, cost i a b (L a b) ≤ (i.2.2.1 : ℤ) - i.2.2.2

open Classical in
/-- PLANAR 3-INDEX ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def planarThreeIndexAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarThreeIndexAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ PlanarThreeIndexAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeIndexAssignment
