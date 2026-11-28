/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.Bandit.ObliviousAdversarial

/-!
# Oblivious adversarial bandit tests

Checks of the action law and the regret on concrete policies and tables: the horizon zero, the
first arm's law, a constant policy (its action law is a point mass, and its regret is zero on a
table where its arm is best), the uniform policy on two arms over two rounds (its expected reward
is the average of the arms' total rewards, its regret is half the gap between them, and it is `1`
on the table where one arm always pays `1` and the other `0`), and an adaptive policy whose regret
is negative on a two-round table.
-/

namespace CSLibExtTest.MachineLearning.Bandit.Adversarial

open Finset Cslib.MachineLearning.Bandit.Adversarial

/-- On a finite measurable space with measurable singletons, the expectation of a real-valued
function `f` under a point mass at `a` is `f a`. -/
theorem expect_pure {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (f : α → ℝ) : (PMF.pure a).expect f = f a := by
  rw [PMF.expect, PMF.toMeasure_pure, MeasureTheory.integral_dirac]

/-- For a real-valued function `f` on `Fin 2`, the `Finset.sup'` over all of `Fin 2`, as used in
`regret`, is `max (f 0) (f 1)`. -/
theorem sup'_univ_fin_two (f : Fin 2 → ℝ) : univ.sup' univ_nonempty f = max (f 0) (f 1) :=
  le_antisymm (sup'_le _ _ fun i _ ↦ by fin_cases i <;> simp)
    (max_le (le_sup' f (mem_univ 0)) (le_sup' f (mem_univ 1)))

/-! ## The horizon zero and the first round -/

/-- With `k ≥ 1` arms, where the regret is defined, every policy has zero regret over zero
rounds. -/
example {k : ℕ} [NeZero k] (π : Policy k) (x : Fin 0 → Fin k → ℝ) : regret π x = 0 := by
  simp [regret, expect_pure]

/-- Over one round, on every reward table, the arm is drawn from the policy's law at the empty
history. -/
example {k : ℕ} (π : Policy k) (x : Fin 1 → Fin k → ℝ) :
    (actionLaw π x).map (fun a ↦ a 0) = π 0 default := by
  rw [actionLaw_succ, actionLaw_zero, PMF.pure_bind, PMF.map_comp]
  have : (fun i : Fin k ↦ (Fin.snoc (default : Fin 0 → Fin k) i : Fin 1 → Fin k) 0) = id := by
    funext i; rfl
  rw [Function.comp_def, this, PMF.map_id, Subsingleton.elim (history (Fin.init x) default)]

/-! ## A constant policy -/

/-- The policy that always chooses arm `i`. -/
noncomputable def constPolicy {k : ℕ} (i : Fin k) : Policy k := fun _ _ ↦ PMF.pure i

/-- On every reward table, the action law of a constant policy is the point mass at the constant
arm sequence. -/
theorem actionLaw_constPolicy {k : ℕ} (i : Fin k) :
    ∀ {n : ℕ} (x : Fin n → Fin k → ℝ), actionLaw (constPolicy i) x = PMF.pure fun _ ↦ i
  | 0, x => by rw [actionLaw_zero]; congr 1; exact Subsingleton.elim _ _
  | n + 1, x => by
    rw [actionLaw_succ, actionLaw_constPolicy i (Fin.init x), PMF.pure_bind, constPolicy,
      PMF.pure_map]
    congr 1
    funext t
    induction t using Fin.lastCases <;> simp

/-- On every reward table, the regret of the constant policy `i` is the gap between the best arm's
total reward and the total reward of arm `i`. -/
theorem regret_constPolicy {k n : ℕ} [NeZero k] (i : Fin k) (x : Fin n → Fin k → ℝ) :
    regret (constPolicy i) x = univ.sup' univ_nonempty (fun j ↦ ∑ t, x t j) - ∑ t, x t i := by
  rw [regret, actionLaw_constPolicy, expect_pure]

/-- The constant policy has zero regret on a table where its arm has the largest total reward. -/
example {k n : ℕ} [NeZero k] (i : Fin k) (x : Fin n → Fin k → ℝ)
    (hi : ∀ j, ∑ t, x t j ≤ ∑ t, x t i) : regret (constPolicy i) x = 0 := by
  rw [regret_constPolicy, sub_eq_zero]
  exact le_antisymm (sup'_le _ _ fun j _ ↦ hi j) (le_sup' (fun j ↦ ∑ t, x t j) (mem_univ i))

/-- On the two-armed table where arm `0` pays `1` and arm `1` pays `0` in every round, the
constant policy `1` has regret `n`. -/
example (n : ℕ) : regret (constPolicy 1) (fun (_ : Fin n) (i : Fin 2) ↦ if i = 0 then 1 else 0)
    = n := by
  simp [regret_constPolicy, sup'_univ_fin_two]

/-! ## The uniform policy on two arms -/

/-- The policy that chooses each of two arms with probability `1/2` in every round, whatever the
history. -/
noncomputable def uniformPolicy : Policy 2 := fun _ _ ↦ PMF.uniformFintype (Fin 2)

/-- On every two-armed reward table with two rounds, the expected reward of the uniform policy is
half the total reward of the two arms. -/
theorem expect_actionLaw_uniformPolicy (x : Fin 2 → Fin 2 → ℝ) :
    (actionLaw uniformPolicy x).expect (fun a ↦ ∑ t, x t (a t)) =
      ((∑ t, x t 0) + (∑ t, x t 1)) / 2 := by
  rw [expect_actionLaw_succ, expect_actionLaw_succ, actionLaw_zero, expect_pure]
  simp only [uniformPolicy, PMF.expect_uniformOfFintype, Fin.sum_univ_two]
  simp [Fin.snoc]
  ring

/-- On every two-armed reward table with two rounds, the regret of the uniform policy is half the
gap between the total rewards of the two arms. -/
example (x : Fin 2 → Fin 2 → ℝ) :
    regret uniformPolicy x = |(∑ t, x t 0) - (∑ t, x t 1)| / 2 := by
  rw [regret, expect_actionLaw_uniformPolicy, sup'_univ_fin_two]
  rcases le_total (∑ t, x t 0) (∑ t, x t 1) with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/-- On the two-round table where arm `0` pays `1` and arm `1` pays `0`, the uniform policy has
regret `1`. -/
example : regret uniformPolicy (fun (_ : Fin 2) (i : Fin 2) ↦ if i = 0 then 1 else 0) = 1 := by
  rw [regret, expect_actionLaw_uniformPolicy, sup'_univ_fin_two]
  norm_num

/-! ## An adaptive policy with negative regret -/

/-- The policy that chooses arm `0` in the first round, and afterwards arm `1` if the first
reward it observed is `1` and arm `0` otherwise. -/
noncomputable def switchPolicy : Policy 2 := fun t h ↦
  PMF.pure (if ht : 0 < t then (if (h ⟨0, ht⟩).2 = 1 then 1 else 0) else 0)

/-- The table on which arm `0` pays `1` in the first round and arm `1` pays `1` in the second;
the other rewards are `0`. -/
def switchTable : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 1]]

/-- On `switchTable`, `switchPolicy` chooses arm `0`, then arm `1`. -/
theorem actionLaw_switchPolicy : actionLaw switchPolicy switchTable = PMF.pure ![0, 1] := by
  rw [actionLaw_succ, actionLaw_succ, actionLaw_zero, PMF.pure_bind]
  simp only [switchPolicy, PMF.pure_map, PMF.pure_bind]
  congr 1
  funext t
  fin_cases t <;> simp [Fin.snoc, Fin.init, switchTable]

/-- Each arm has total reward `1` on `switchTable`, while `switchPolicy` collects `2`: its regret
is `-1`. The regret against an oblivious adversary can be negative. -/
example : regret switchPolicy switchTable = -1 := by
  rw [regret, actionLaw_switchPolicy, expect_pure, sup'_univ_fin_two]
  norm_num [switchTable]

end CSLibExtTest.MachineLearning.Bandit.Adversarial
