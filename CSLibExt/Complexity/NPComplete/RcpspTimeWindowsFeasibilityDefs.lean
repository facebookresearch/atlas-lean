/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROJECT SCHEDULING WITH RESOURCES AND TIME WINDOWS: FEASIBILITY: definitions

Source:
M. Bartusch, R. H. Möhring and F. J. Radermacher, "Scheduling project networks with resource
constraints and time windows", Annals of Operations Research 16 (1988), 201-240,
doi:10.1007/BF02283745;
S. Hartmann and D. Briskorn, "A survey of variants and extensions of the resource-constrained
project scheduling problem", European Journal of Operational Research 207 (2010), 1-14,
doi:10.1016/j.ejor.2009.11.005, Section 3.2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RcpspTimeWindowsFeasibility

/-- An instance: the activities as pairs `(p_j, [r_{j0}, …, r_{j(K-1)}])` of duration and
resource requirements, the capacities `[R_0, …, R_{K-1}]`, and the time lags as tuples
`(i, j, a, b)` standing for `S_j - S_i ≥ a - b`. -/
abbrev RcpspTimeWindowsFeasibilityInstance :=
  List (ℕ × List ℕ) × List ℕ × List (ℕ × ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: every activity lists one requirement per resource, and
every time lag joins two activities. -/
def WellFormed (i : RcpspTimeWindowsFeasibilityInstance) : Prop :=
  (∀ a ∈ i.1, a.2.length = i.2.1.length) ∧
    ∀ l ∈ i.2.2, l.1 < i.1.length ∧ l.2.1 < i.1.length

/-- The activities in process in period `t` under start times `S`. -/
def inProcess (i : RcpspTimeWindowsFeasibilityInstance) (S : Fin i.1.length → ℕ) (t : ℕ) :
    Finset (Fin i.1.length) :=
  Finset.univ.filter (fun j => S j ≤ t ∧ t < S j + (i.1.get j).1)

/-- There are start times `S` satisfying every time lag such that in every period `t` the
activities in process require at most `R_k` units of every resource `k`. -/
def RcpspTimeWindowsFeasibilityFeasible (i : RcpspTimeWindowsFeasibilityInstance) : Prop :=
  ∃ S : Fin i.1.length → ℕ,
    (∀ l ∈ i.2.2, ∀ a b : Fin i.1.length, a.val = l.1 → b.val = l.2.1 →
      (l.2.2.1 : ℤ) - l.2.2.2 ≤ (S b : ℤ) - S a) ∧
    ∀ k < i.2.1.length, ∀ t : ℕ,
      ∑ j ∈ inProcess i S t, (i.1.get j).2.getD k 0 ≤ i.2.1.getD k 0

open Classical in
/-- PROJECT SCHEDULING WITH RESOURCES AND TIME WINDOWS: FEASIBILITY as a decision problem over
bitstrings. -/
noncomputable def rcpspTimeWindowsFeasibilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RcpspTimeWindowsFeasibilityInstance) x with
  | some i => decide (WellFormed i ∧ RcpspTimeWindowsFeasibilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RcpspTimeWindowsFeasibility
