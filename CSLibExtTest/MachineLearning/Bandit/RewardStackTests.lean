/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.MachineLearning.Bandit.RewardStack

/-!
# Reward-stack model tests

Checks of the reward-stack model on concrete instances and edge cases: the horizon zero, the law
and the independence of the stack entries at every horizon, the restriction to an earlier
horizon, the law of the first arm, a policy that always pulls the same arm, whose first two
rewards are the first two entries of that arm's stack, and a bandit with point-mass rewards, on
which every reward is almost surely the value of the chosen arm.
-/

namespace CSLibExtTest.MachineLearning.Bandit.RewardStack

open MeasureTheory ProbabilityTheory Finset Cslib.MachineLearning.Bandit

variable {k : ℕ} (ν : StochasticBandit k) (π : Policy k)

/-! ## Structure of the model -/

example (n : ℕ) : IsProbabilityMeasure (rewardStackLaw ν π n) := inferInstance

/-- At horizon zero the history is the empty one: its law is the point mass. -/
example : (rewardStackLaw ν π 0).map Prod.snd = Measure.dirac default := by
  rw [rewardStackLaw_zero, Measure.map_map measurable_snd (by fun_prop)]
  simp [Function.comp_def]

/-- At every horizon, each stack entry has its arm's reward law. -/
theorem map_entry_rewardStackLaw (n s : ℕ) (i : Fin k) :
    (rewardStackLaw ν π n).map (fun p ↦ p.1 s i) = ν.law i := by
  rw [← map_stack_apply ν s i, ← map_fst_rewardStackLaw ν π n,
    Measure.map_map (g := fun x : ℕ → Fin k → ℝ ↦ x s i)
      ((measurable_pi_apply i).comp (measurable_pi_apply s)) measurable_fst]
  rfl

/-- Two entries of one arm's stack are independent. -/
example (i : Fin k) :
    IndepFun (fun x : ℕ → Fin k → ℝ ↦ x 0 i) (fun x ↦ x 1 i)
      (Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law) :=
  (iIndepFun_stack ν).indepFun (i := (0, i)) (j := (1, i)) (by simp)

/-- Restricting a horizon-three model to its first round gives the horizon-one model. -/
example : (rewardStackLaw ν π 3).map (Prod.map id (Fin.take 1 (by norm_num))) =
    rewardStackLaw ν π 1 :=
  map_take_rewardStackLaw ν π _

/-- The arm of the first round has the law of the policy's first kernel at the empty history. -/
example : (rewardStackLaw ν π 1).map (fun p ↦ (p.2 0).1) = π.kernel 0 default := by
  have hconst : Kernel.prodMkLeft (ℕ → Fin k → ℝ) (π.kernel 0) =
      Kernel.const _ (π.kernel 0 default) := by
    ext p : 1
    simp [Subsingleton.elim p.2 default]
  have hm : Measurable (fun p : (ℕ → Fin k → ℝ) × History k 1 ↦
      ((p.1, Fin.take (0 : Fin 1) (Fin.isLt 0).le p.2), (p.2 0).1)) :=
    (measurable_fst.prodMk ((History.measurable_take _ _).comp measurable_snd)).prodMk
      ((measurable_pi_apply 0).comp measurable_snd).fst
  have key : (fun p : (ℕ → Fin k → ℝ) × History k 1 ↦ (p.2 0).1) =
      Prod.snd ∘ fun p ↦ ((p.1, Fin.take (0 : Fin 1) (Fin.isLt 0).le p.2), (p.2 0).1) := rfl
  rw [key, ← Measure.map_map measurable_snd hm, map_take_action_rewardStackLaw ν π (0 : Fin 1)]
  change (rewardStackLaw ν π 0 ⊗ₘ Kernel.prodMkLeft (ℕ → Fin k → ℝ) (π.kernel 0)).snd = _
  rw [Measure.snd_compProd, hconst, Measure.const_comp, measure_univ, one_smul]

/-! ## A policy that always pulls the same arm -/

/-- The policy that always pulls arm `i`. -/
noncomputable def constPolicy (i : Fin k) : Policy k where
  kernel _ := Kernel.const _ (Measure.dirac i)
  isMarkovKernel_kernel _ := inferInstance

/-- Under the policy that always pulls arm `i`, every round's arm is `i` almost surely. -/
theorem ae_action_constPolicy (i : Fin k) {n : ℕ} (t : Fin n) :
    ∀ᵐ p ∂rewardStackLaw ν (constPolicy i) n, (p.2 t).1 = i := by
  have hm : Measurable (fun p : (ℕ → Fin k → ℝ) × History k n ↦
      ((p.1, Fin.take t t.isLt.le p.2), (p.2 t).1)) :=
    (measurable_fst.prodMk ((History.measurable_take _ _).comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp measurable_snd).fst
  have h : ∀ᵐ q ∂(rewardStackLaw ν (constPolicy i) n).map
      (fun p ↦ ((p.1, Fin.take t t.isLt.le p.2), (p.2 t).1)), q.2 = i := by
    rw [map_take_action_rewardStackLaw]
    refine Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun measurable_snd measurable_const)
      (ae_of_all _ fun p ↦ ?_)
    simp [constPolicy, ae_dirac_eq]
  exact ae_of_ae_map hm.aemeasurable h

/-- When arm `0` is always pulled, the first reward is the first entry of arm `0`'s stack and the
second reward is the second entry: each pull reads the next unused entry. -/
example (hk : 0 < k) :
    ∀ᵐ p ∂rewardStackLaw ν (constPolicy ⟨0, hk⟩) 2,
      (p.2 0).2 = p.1 0 ⟨0, hk⟩ ∧ (p.2 1).2 = p.1 1 ⟨0, hk⟩ := by
  filter_upwards [ae_action_constPolicy ν ⟨0, hk⟩ (0 : Fin 2),
    ae_action_constPolicy ν ⟨0, hk⟩ (1 : Fin 2), ae_reward_eq_stack ν _ (0 : Fin 2),
    ae_reward_eq_stack ν _ (1 : Fin 2)] with p h0 h1 r0 r1
  refine ⟨?_, ?_⟩
  · rw [r0, h0]
    simp [pullCount_eq_sum]
  · have hc : pullCount (⟨0, hk⟩ : Fin k)
        (Fin.take ((1 : Fin 2) : ℕ) (Fin.isLt 1).le p.2 : History k 1) = 1 := by
      rw [pullCount_eq_sum]
      show (∑ t : Fin 1, if (p.2 (Fin.castLE (by norm_num) t)).1 = ⟨0, hk⟩ then 1 else 0) = 1
      rw [Fin.sum_univ_one]
      exact ite_eq_left h0
    rw [r1, h1, hc]

/-! ## Point-mass rewards -/

/-- The bandit whose arm `i` always pays `c i`. -/
noncomputable def diracBandit (c : Fin k → ℝ) : StochasticBandit k where
  law i := Measure.dirac (c i)
  isProbabilityMeasure_law _ := inferInstance

/-- When arm `i` always pays `c i`, the reward of every round is almost surely the value of the
arm chosen in it, whatever the policy. -/
example (c : Fin k → ℝ) (n : ℕ) (t : Fin n) :
    ∀ᵐ p ∂rewardStackLaw (diracBandit c) π n, (p.2 t).2 = c (p.2 t).1 := by
  have hstack : ∀ᵐ p ∂rewardStackLaw (diracBandit c) π n, ∀ s i, p.1 s i = c i := by
    refine ae_all_iff.2 fun s ↦ ae_all_iff.2 fun i ↦ ?_
    have h : ∀ᵐ y ∂(rewardStackLaw (diracBandit c) π n).map (fun p ↦ p.1 s i), y = c i := by
      rw [map_entry_rewardStackLaw]
      simp [diracBandit, ae_dirac_eq]
    exact ae_of_ae_map ((measurable_pi_apply i).comp
      ((measurable_pi_apply s).comp measurable_fst)).aemeasurable h
  filter_upwards [hstack, ae_reward_eq_stack (diracBandit c) π t] with p hp hr
  rw [hr, hp]

end CSLibExtTest.MachineLearning.Bandit.RewardStack
