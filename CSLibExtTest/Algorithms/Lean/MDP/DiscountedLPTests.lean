/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.DiscountedLP
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Regression tests for discounted LP duality

A one-state chain distinguishes the reward of the LP table from that of the normalized
occupancy. An asymmetric two-state example recovers a genuinely randomized policy from a
flow specified independently of any policy. At zero discount, the state marginal is just the
initial weighting, so row recovery can fail without strict positivity.
-/

namespace Cslib.Algorithms.Lean.MarkovDecision.DiscountedLP

private theorem half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num

private def oneState : MDP Unit Unit ℝ where
  prob _ _ _ := 1
  reward _ _ := 1

private theorem one_stochastic : oneState.Stochastic :=
  ⟨fun _ _ _ => zero_le_one, fun _ _ => by simp [oneState]⟩

private def onlyRow : Unit → Unit → ℝ := fun _ _ => 1
private theorem onlyRow_stochastic : IsRowStochastic onlyRow :=
  ⟨fun _ _ => zero_le_one, fun _ => by simp [onlyRow]⟩

/-- Both attained LP values are two; the normalized occupancy has reward one. -/
example :
    let w := fun _ : Unit => (1 : ℝ)
    let π : {π : Unit → Unit → ℝ // IsRowStochastic π} := ⟨onlyRow, onlyRow_stochastic⟩
    let d := occupancyEquiv one_stochastic half_nonneg half_lt_one (w := w) (fun _ => zero_lt_one) π
    (∑ s, w s * optimalValue oneState (1 / 2) one_stochastic half_nonneg half_lt_one s) = 2 ∧
    (∑ p, d.val p) = 2 ∧ (∑ p, d.val p * oneState.reward p.1 p.2) = 2 ∧
    (∑ p, occupancy oneState (1 / 2) one_stochastic half_nonneg half_lt_one π.val π.property w p *
      oneState.reward p.1 p.2) = 1 := by
  dsimp only
  have mass {d : Unit × Unit → ℝ} (hd : DualFeasible oneState (1 / 2) (fun _ => 1) d) :
      d ((), ()) = 2 := by
    have h := hd.total_mass one_stochastic half_lt_one
    norm_num [Fintype.sum_prod_type] at h
    exact h
  obtain ⟨d, hd, heq⟩ := (weighted_duality one_stochastic half_nonneg half_lt_one
    (w := fun _ => 1) (fun _ => zero_lt_one)).2.2.2.1
  have hc := mass (dualFeasible_occupancy_div one_stochastic half_nonneg half_lt_one
    onlyRow_stochastic (w := fun _ => 1) (fun _ => zero_le_one))
  have ho : occupancy oneState (1 / 2) one_stochastic half_nonneg half_lt_one onlyRow
      onlyRow_stochastic (fun _ => 1) ((), ()) = 1 := by norm_num at hc; linarith
  constructor
  · rw [← heq]
    simpa [Fintype.sum_prod_type, oneState] using mass hd
  · simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    exact ⟨hc, (mul_one _).trans hc, (mul_one _).trans ho⟩

private abbrev St := Fin 2
private abbrev Ac := Fin 2

/-- State 1 is absorbing; from state 0 only action 1 moves to state 1. -/
private noncomputable def twoState : MDP St Ac ℝ where
  prob := ![![![1, 0], ![0, 1]], ![![0, 1], ![0, 1]]]
  reward := ![![-1, 2], ![3, -2]]

private theorem two_stochastic : twoState.Stochastic := by
  constructor
  · intro s a t; fin_cases s <;> fin_cases a <;> fin_cases t <;> norm_num [twoState]
  · intro s a; fin_cases s <;> fin_cases a <;> norm_num [twoState, Fin.sum_univ_two]

private def weights : St → ℝ := ![3, 2]
private theorem weights_pos (s : St) : 0 < weights s := by fin_cases s <;> norm_num [weights]

private noncomputable def table (p : St × Ac) : ℝ := (![![2, 2], ![3/2, 9/2]] : St → Ac → ℝ) p.1 p.2

private theorem table_feasible : DualFeasible twoState (1/2) weights table := by
  constructor
  · rintro ⟨s, a⟩; fin_cases s <;> fin_cases a <;> norm_num [table]
  · intro t
    fin_cases t <;> norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, twoState, table, weights]

/-- The feasible value `(5,6)` and a flow choosing action 1 at state 0 and action 0 at state 1
both have objective 27. Weak duality and strict primal minimality recover the Bellman value. -/
example : optimalValue twoState (1/2) two_stochastic half_nonneg half_lt_one = ![5, 6] := by
  let V : St → ℝ := ![5, 6]
  let d (p : St × Ac) : ℝ := (![![0, 3], ![7, 0]] : St → Ac → ℝ) p.1 p.2
  have hV : PrimalFeasible twoState (1/2) V := by
    intro s a; fin_cases s <;> fin_cases a <;> norm_num [qValue, twoState, V, Fin.sum_univ_two]
  have hd : DualFeasible twoState (1/2) weights d := by
    constructor
    · rintro ⟨s, a⟩; fin_cases s <;> fin_cases a <;> norm_num [d]
    · intro t
      fin_cases t <;> norm_num [twoState, weights, d, Fin.sum_univ_two, Fintype.sum_prod_type]
  have hmatch : ∑ s, weights s * V s = ∑ p, d p * twoState.reward p.1 p.2 := by
    norm_num [twoState, weights, V, d, Fin.sum_univ_two, Fintype.sum_prod_type]
  by_contra h
  have hs := lt_primal_cost two_stochastic half_nonneg half_lt_one weights_pos hV (Ne.symm h)
  exact hs.not_ge (hmatch.trans_le (weak_duality (isLeast_primalFeasible _ _ _).1 hd))

private noncomputable def mixedRows : St → Ac → ℝ := ![![1/2, 1/2], ![1/4, 3/4]]
private theorem mixed_stochastic : IsRowStochastic mixedRows := by
  constructor
  · intro s a; fin_cases s <;> fin_cases a <;> norm_num [mixedRows]
  · intro s; fin_cases s <;> norm_num [mixedRows, Fin.sum_univ_two]

/-- Row normalization recovers different mixtures in the two states. Applying the equivalence
back to those rows produces every entry of the prescribed table, not merely its total mass. -/
example :
    let e := occupancyEquiv two_stochastic half_nonneg half_lt_one weights_pos
    (e.symm ⟨table, table_feasible⟩).val = mixedRows ∧
    (∀ p, occupancy twoState (1/2) two_stochastic half_nonneg half_lt_one mixedRows
      mixed_stochastic weights p / (1 - 1/2) = table p) ∧
    ¬ ∃ f : St → Ac, mixedRows = detPolicy f := by
  let e := occupancyEquiv two_stochastic half_nonneg half_lt_one weights_pos
  have recover : e.symm ⟨table, table_feasible⟩ = ⟨mixedRows, mixed_stochastic⟩ := by
    apply Subtype.ext
    funext s a
    change table (s, a) / (∑ b, table (s, b)) = mixedRows s a
    fin_cases s <;> fin_cases a <;> norm_num [table, mixedRows, Fin.sum_univ_two]
  refine ⟨congrArg Subtype.val recover, ?_, ?_⟩
  · intro p
    exact congrArg (fun x => x.val p) ((congrArg e recover).symm.trans (e.apply_symm_apply _))
  · rintro ⟨f, h⟩
    have hh := congrFun (congrFun h 0) 0
    change (1/2 : ℝ) = (if (0 : Ac) = f 0 then 1 else 0) at hh
    split at hh <;> norm_num at hh

/-- With initial mass five, the probability-weight flow has one fifth the mass and reward.
The mixed policy's reward is negative, so this also tests signed objective scaling. -/
example : ∃ e, DualFeasible twoState (1/2) (fun s => weights s / 5) e ∧
    table = (fun p => 5 * e p) ∧ (∑ p, e p * twoState.reward p.1 p.2) = -(1/2) := by
  have hW : ∑ s, weights s = 5 := by norm_num [Fin.sum_univ_two, weights]
  have h := normalize_weights twoState (1/2) weights_pos
  dsimp only at h
  rw [hW] at h
  obtain ⟨e, he, htable⟩ := (h.2.2.1 table).mp table_feasible
  refine ⟨e, he, htable, ?_⟩
  have hr : ∑ p, table p * twoState.reward p.1 p.2 = -(5/2) := by
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, table, twoState]
  rw [htable, h.2.2.2.2] at hr
  linarith

/-- At zero discount a zero-weight state can have no mass. Two different policies, agreeing
on the positive-weight state, then have exactly the same occupancy. -/
example : ∃ π τ : St → Ac, π ≠ τ ∧ ∀ p,
    occupancy twoState 0 two_stochastic le_rfl zero_lt_one (detPolicy π)
        (isRowStochastic_detPolicy π) (![1, 0] : St → ℝ) p =
      occupancy twoState 0 two_stochastic le_rfl zero_lt_one (detPolicy τ)
        (isRowStochastic_detPolicy τ) (![1, 0] : St → ℝ) p := by
  let π : St → Ac := fun _ => 0
  let τ : St → Ac := id
  let d (p : St × Ac) : ℝ := if p = (0, 0) then 1 else 0
  have hd : DualFeasible twoState 0 (![1, 0] : St → ℝ) d := by
    refine ⟨fun p => by dsimp [d]; split <;> norm_num, ?_⟩
    intro t; fin_cases t <;> norm_num [d, Fin.sum_univ_two]
  have occ (f : St → Ac) (h : f 0 = 0) (p : St × Ac) :
      occupancy twoState 0 two_stochastic le_rfl zero_lt_one (detPolicy f)
        (isRowStochastic_detPolicy f) (![1, 0] : St → ℝ) p = d p := by
    have hf (s : St) (a : Ac) : d (s, a) = (![1, 0] : St → ℝ) s * detPolicy f s a := by
      fin_cases s <;> fin_cases a <;> simp [d, detPolicy, h]
    simpa using occupancy_div_eq_of_factor two_stochastic le_rfl zero_lt_one
      (isRowStochastic_detPolicy f) hd _ hf p
  exact ⟨π, τ, fun h => by simpa [π, τ] using congrFun h 1,
    fun p => (occ π rfl p).trans (occ τ rfl p).symm⟩

end Cslib.Algorithms.Lean.MarkovDecision.DiscountedLP
