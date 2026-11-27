/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.SoftmaxPolicyGradientConvergence

/-! Regression at zero discount and the largest step size in the theorem. -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Filter StochasticPolicy
open scoped Topology

private def bandit : MDP Unit Bool ℝ where
  reward _ a := if a then 1 else 0
  prob _ _ _ := 1

private theorem bandit_stochastic : bandit.Stochastic := by
  constructor
  · intro _ _ _
    exact zero_le_one
  · intro _ _
    simp [bandit]

private theorem discount_nonneg : (0 : ℝ) ≤ 0 := le_rfl
private theorem discount_lt_one : (0 : ℝ) < 1 := zero_lt_one

private theorem bandit_optimal : optimalValue bandit 0 bandit_stochastic discount_nonneg
    discount_lt_one () = 1 := by
  have hfixed : bellman bandit 0 (fun _ => 1) = fun _ => 1 := by
    funext s
    apply le_antisymm
    · apply sup'_le
      intro a _
      cases a <;> simp [qValue, bandit]
    · calc 1 = qValue bandit 0 (fun _ => 1) s true := by simp [qValue, bandit]
        _ ≤ bellman bandit 0 (fun _ => 1) s :=
          le_sup' (qValue bandit 0 (fun _ => 1) s) (mem_univ true)
  exact (congrFun (eq_optimalValue_of_bellman_eq bandit_stochastic discount_nonneg
    discount_lt_one hfixed) ()).symm

example : Tendsto (fun t => stochValue bandit 0 bandit_stochastic discount_nonneg
      discount_lt_one (softmax (softmaxPGLogits bandit_stochastic discount_nonneg
        discount_lt_one (fun _ => 1) (1 / 8) t)) ()) atTop (𝓝 1) := by
  have h := tendsto_stochValue_softmaxPGLogits bandit_stochastic discount_nonneg
    discount_lt_one (by intro _ a; cases a <;> simp [bandit]) (fun _ => 1)
    (fun _ => zero_lt_one) (by simp) (η := 1 / 8) (by norm_num) (by norm_num) ()
  simpa only [bandit_optimal] using h

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
