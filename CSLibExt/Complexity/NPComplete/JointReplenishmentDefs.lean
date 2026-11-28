/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# JOINT REPLENISHMENT (FINITE HORIZON): definitions

Source:
E. Arkin, D. Joneja, and R. Roundy, "Computational complexity of uncapacitated multi-echelon
production planning problems", Operations Research Letters 8 (1989), 61-66,
doi:10.1016/0167-6377(89)90001-1;
M. Bienkowski, J. Byrka, M. Chrobak, N. Dobbs, T. Nowicki, M. Sviridenko, G. Świrszcz, and
N. E. Young, "Approximation algorithms for the joint replenishment problem with deadlines",
Journal of Scheduling 18 (2015), 545-560, doi:10.1007/s10951-014-0392-y (records that the
problem is NP-complete even with linear waiting costs, crediting Arkin, Joneja, and Roundy).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.JointReplenishment

/-- An instance: the number `T` of periods, the demands (one row per item, entry `t` of row `i`
is `d_{i,t}`), the holding costs `h_i` and the minor ordering costs `k_i` of the items in order,
the major ordering cost `K₀`, and the bound `B`. -/
abbrev JointReplenishmentInstance := ℕ × List (List ℕ) × List ℕ × List ℕ × ℕ × ℕ

/-- The number `N` of items: the number of demand rows. -/
def numItems (i : JointReplenishmentInstance) : ℕ := i.2.1.length

/-- The demand `d_{a,t}` of item `a` in period `t`. -/
def demand (i : JointReplenishmentInstance) (a t : ℕ) : ℕ := (i.2.1.getD a []).getD t 0

/-- The holding cost `h_a` of item `a`. -/
def holdingCost (i : JointReplenishmentInstance) (a : ℕ) : ℕ := i.2.2.1.getD a 0

/-- The minor ordering cost `k_a` of item `a`. -/
def minorCost (i : JointReplenishmentInstance) (a : ℕ) : ℕ := i.2.2.2.1.getD a 0

/-- Well-formedness of an instance: every demand row has `T` entries, and there is one holding
cost and one minor ordering cost per item. -/
def WellFormed (i : JointReplenishmentInstance) : Prop :=
  (∀ row ∈ i.2.1, row.length = i.1) ∧ i.2.2.1.length = numItems i ∧
    i.2.2.2.1.length = numItems i

/-- The units of item `a` ordered in periods `0, …, t` under the plan `x`. -/
def ordered (i : JointReplenishmentInstance) (x : Fin (numItems i) → Fin i.1 → ℕ)
    (a : Fin (numItems i)) (t : Fin i.1) : ℕ :=
  ∑ s with s ≤ t, x a s

/-- The demand of item `a` in periods `0, …, t`. -/
def demanded (i : JointReplenishmentInstance) (a : Fin (numItems i)) (t : Fin i.1) : ℕ :=
  ∑ s : Fin i.1 with s ≤ t, demand i a s

/-- The cost of the plan `x`: the major cost `K₀` for each period with an order, the minor cost
`k_a` for each period with an order of item `a`, and `h_a` per unit of item `a` in stock at the
end of each period (the stock is `ordered - demanded`, nonnegative for a plan without
backlogging). -/
def planCost (i : JointReplenishmentInstance) (x : Fin (numItems i) → Fin i.1 → ℕ) : ℕ :=
  (∑ t : Fin i.1, if ∃ a, x a t ≠ 0 then i.2.2.2.2.1 else 0) +
    (∑ a : Fin (numItems i), ∑ t : Fin i.1, if x a t ≠ 0 then minorCost i a else 0) +
      ∑ a : Fin (numItems i), ∑ t : Fin i.1,
        holdingCost i a * (ordered i x a t - demanded i a t)

/-- Some ordering plan meets every demand without backlogging and costs at most `B`. -/
def JointReplenishmentFeasible (i : JointReplenishmentInstance) : Prop :=
  ∃ x : Fin (numItems i) → Fin i.1 → ℕ,
    (∀ a t, demanded i a t ≤ ordered i x a t) ∧ planCost i x ≤ i.2.2.2.2.2

open Classical in
/-- JOINT REPLENISHMENT (FINITE HORIZON) as a decision problem over bitstrings. -/
noncomputable def jointReplenishmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := JointReplenishmentInstance) x with
  | some i => decide (WellFormed i ∧ JointReplenishmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.JointReplenishment
