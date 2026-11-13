/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Approximation.KnapsackScaling
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Tests for knapsack profit scaling

`optVal` is evaluated by unfolding its definition on a two-item instance at
three capacities. The scaling bound is then applied with `K = 2` and `K = 3`:
at `K = 2` the rounded profits single out the true optimum, and at `K = 3`
rounding creates a tie, so a set that is optimal for the rounded profits can
lose true profit, within `n * K`; the bound for an arbitrary rounded-optimal set
covers that set. Finally the bound is applied, through the item-list API, to the
set that the verified dynamic program `solve` returns on the rounded values.
-/

namespace CSLibExtTest.Algorithms.Lean.Approximation.KnapsackScaling

open Cslib.Algorithms.Lean.TimeM.Knapsack

/-- Weights of the two-item instance. -/
def w₂ : Fin 2 → ℕ := ![1, 1]

/-- Profits of the two-item instance. -/
def p₂ : Fin 2 → ℕ := ![10, 9]

/-- Profits that rounding by `K = 3` makes equal (`5 / 3 = 4 / 3 = 1`). -/
def q₂ : Fin 2 → ℕ := ![5, 4]

/-- Capacity `0`: only the empty set is feasible. -/
example : optVal w₂ p₂ 0 = 0 := by decide +kernel

/-- Capacity `1`: one item fits, and the better one has profit `10`. -/
example : optVal w₂ p₂ 1 = 10 := by decide +kernel

/-- Capacity `2`: both items fit. -/
example : optVal w₂ p₂ 2 = 19 := by decide +kernel

/-- `le_optVal` on the feasible set `{1}`. -/
example : (∑ i ∈ ({1} : Finset (Fin 2)), p₂ i) ≤ optVal w₂ p₂ 1 :=
  le_optVal w₂ p₂ 1 (by decide +kernel)

/-- At `K = 2` the rounded profits are `5` and `4`, so `{0}` is the only
feasible set that is optimal for them. -/
theorem eq_singleton_zero_of_scaled_opt (S : Finset (Fin 2))
    (hS : (∑ i ∈ S, w₂ i) ≤ 1)
    (hopt : ∀ T : Finset (Fin 2), (∑ i ∈ T, w₂ i) ≤ 1 →
      ∑ i ∈ T, p₂ i / 2 ≤ ∑ i ∈ S, p₂ i / 2) :
    S = {0} := by
  revert S
  decide +kernel

/-- `knapsack_scaling_loss` at `K = 2`, with all three conclusions: the set it
provides is feasible, optimal for the rounded profits, and within `2 * 2` of
the optimum. -/
example : ∃ S : Finset (Fin 2), (∑ i ∈ S, w₂ i) ≤ 1 ∧
    (∀ T : Finset (Fin 2), (∑ i ∈ T, w₂ i) ≤ 1 →
      ∑ i ∈ T, p₂ i / 2 ≤ ∑ i ∈ S, p₂ i / 2) ∧
    optVal w₂ p₂ 1 ≤ (∑ i ∈ S, p₂ i) + 2 * 2 :=
  knapsack_scaling_loss w₂ p₂ 1 2 (by norm_num)

/-- At `K = 2` the set provided by `knapsack_scaling_loss` is forced to be
`{0}`, whose true profit is the optimum. -/
example : ∃ S : Finset (Fin 2), S = {0} ∧ optVal w₂ p₂ 1 = ∑ i ∈ S, p₂ i := by
  obtain ⟨S, hS, hopt, -⟩ := knapsack_scaling_loss w₂ p₂ 1 2 (by norm_num)
  exact ⟨S, eq_singleton_zero_of_scaled_opt S hS hopt, by
    rw [eq_singleton_zero_of_scaled_opt S hS hopt]
    decide +kernel⟩

/-- At `K = 3` both rounded profits are `1`: the set `{1}` is feasible and
optimal for the rounded profits, yet its true profit `4` is below
`optVal w₂ q₂ 1 = 5`. -/
example : (∑ i ∈ ({1} : Finset (Fin 2)), w₂ i) ≤ 1 ∧
    (∀ T : Finset (Fin 2), (∑ i ∈ T, w₂ i) ≤ 1 →
      ∑ i ∈ T, q₂ i / 3 ≤ ∑ i ∈ ({1} : Finset (Fin 2)), q₂ i / 3) ∧
    (∑ i ∈ ({1} : Finset (Fin 2)), q₂ i) < optVal w₂ q₂ 1 := by
  decide +kernel

/-- The bound for an arbitrary rounded-optimal set applies to that tied set
`{1}`, which is not optimal: its loss `1` is within `2 * 3`. -/
example : optVal w₂ q₂ 1 ≤ (∑ i ∈ ({1} : Finset (Fin 2)), q₂ i) + 2 * 3 :=
  optVal_le_add_of_scaledOpt w₂ q₂ 1 3 (by norm_num) (by decide +kernel)

/-- The two-item instance as items `⟨weight, value⟩` of the dynamic program. -/
def items₂ : List Item := [⟨1, 10⟩, ⟨1, 9⟩]

/-- `items₂` with values rounded down by `K = 2`. -/
def rounded₂ : List Item := [⟨1, 5⟩, ⟨1, 4⟩]

/-- The dynamic program on the rounded values selects the first item. -/
example : (solve rounded₂ 1).ret.chosen = {⟨0, by decide⟩} := by decide

/-- The bound through the item-list API, for the set `solve` returns on the
rounded values: every feasible set of `items₂` has value at most that set's
true value plus `2 * 2`. -/
example (T : Finset (Fin items₂.length)) (hT : Feasible items₂ 1 T) :
    totalValue items₂ T ≤
      totalValue items₂ (solve rounded₂ 1).ret.chosen + items₂.length * 2 :=
  totalValue_le_add_of_scaledOpt items₂ 1 2 (by norm_num)
    (by unfold Feasible; decide +kernel) hT

end CSLibExtTest.Algorithms.Lean.Approximation.KnapsackScaling
