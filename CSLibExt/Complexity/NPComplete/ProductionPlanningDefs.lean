/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRODUCTION PLANNING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS21] PRODUCTION
PLANNING;
M. Florian, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Deterministic production
planning: algorithms and complexity", Management Science 26 (1980), 669-679,
doi:10.1287/mnsc.26.7.669.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProductionPlanning

/-- An instance: the number `n` of periods, the periods as tuples `(rᵢ, cᵢ, bᵢ, pᵢ, hᵢ)` of
demand, capacity, set-up cost, incremental production cost and inventory cost, and the bound
`B`. -/
abbrev ProductionPlanningInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `n ∈ ℤ⁺`, there are exactly `n` periods, and
`B ∈ ℤ⁺`. -/
def WellFormed (i : ProductionPlanningInstance) : Prop :=
  0 < i.1 ∧ i.2.1.length = i.1 ∧ 0 < i.2.2

/-- The inventory level `I_k = ∑_{j ≤ k} (x_j - r_j)` at the end of period `k`. -/
def inventory (i : ProductionPlanningInstance) (x : Fin i.2.1.length → ℕ)
    (k : Fin i.2.1.length) : ℤ :=
  ∑ j ∈ Finset.univ.filter (· ≤ k), ((x j : ℤ) - (i.2.1.get j).1)

/-- There are production amounts within capacity whose inventory levels are nonnegative and
whose total production, inventory and set-up cost is at most `B`. -/
def ProductionPlanningFeasible (i : ProductionPlanningInstance) : Prop :=
  ∃ x : Fin i.2.1.length → ℕ,
    (∀ k, x k ≤ (i.2.1.get k).2.1) ∧ (∀ k, 0 ≤ inventory i x k) ∧
      ∑ k, (((i.2.1.get k).2.2.2.1 : ℤ) * x k + (i.2.1.get k).2.2.2.2 * inventory i x k) +
          ∑ k ∈ Finset.univ.filter (fun k => 0 < x k), ((i.2.1.get k).2.2.1 : ℤ) ≤ i.2.2

open Classical in
/-- PRODUCTION PLANNING as a decision problem over bitstrings. -/
noncomputable def productionPlanningDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProductionPlanningInstance) x with
  | some i => decide (WellFormed i ∧ ProductionPlanningFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ProductionPlanning
