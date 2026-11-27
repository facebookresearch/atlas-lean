/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.MDP.PolicyGradient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic.NormNum

/-! # Regressions for the general policy gradient theorem -/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.MDP.PolicyGradient

open Cslib.Algorithms.Lean.MarkovDecision
open Cslib.Algorithms.Lean.MarkovDecision.Simplex
open Cslib.Algorithms.Lean.MarkovDecision.Simplex.StochasticPolicy

private def bandit : MDP Unit Bool ℝ where
  reward _ b := if b then 1 else 0
  prob _ _ _ := 1

private theorem bandit_stochastic : bandit.Stochastic := by
  constructor <;> simp [bandit]

private noncomputable def coinPolicy (t : ℝ) : StochasticPolicy Unit Bool :=
  mix (Real.sigmoid t) (Real.sigmoid_nonneg t) (Real.sigmoid_le_one t)
    (ofDet fun _ => false) (ofDet fun _ => true)

private theorem coin_prob (t : ℝ) (s : Unit) (a : Bool) :
    (coinPolicy t).prob s a = if a then Real.sigmoid t else 1 - Real.sigmoid t := by
  cases a <;> simp [coinPolicy, mix_prob, ofDet_prob]

private noncomputable def D (_ : Unit) (a : Bool) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (if a then 1 / 4 else -(1 / 4))

private theorem coin_deriv (s : Unit) (a : Bool) :
    HasFDerivAt (fun t => (coinPolicy t).prob s a) (D s a) 0 := by
  have h := Real.hasDerivAt_sigmoid 0
  cases a
  · convert ((HasDerivAt.const_sub 1 h).hasFDerivAt) using 1 <;>
      norm_num [coin_prob, D, Real.sigmoid_zero]
  · convert h.hasFDerivAt using 1 <;> norm_num [coin_prob, D, Real.sigmoid_zero]

private theorem coin_positive (s : Unit) (a : Bool) : 0 < (coinPolicy 0).prob s a := by
  cases a <;> norm_num [coin_prob, Real.sigmoid_zero]

private theorem halfValue (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    stochValue bandit (1 / 2) bandit_stochastic h₀ h₁ (coinPolicy 0) = fun _ => 1 := by
  symm
  apply eq_stochValue
  intro s
  norm_num [Fintype.sum_bool, qValue, bandit, coin_prob, Real.sigmoid_zero]

private theorem halfQ (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) (s : Unit) (a : Bool) :
    stochQValue bandit_stochastic h₀ h₁ (coinPolicy 0) s a = if a then 3 / 2 else 1 / 2 := by
  unfold stochQValue
  rw [halfValue]
  cases a <;> norm_num [qValue, bandit]

private theorem unit_occupancy {γ : ℝ} (h₀ : 0 ≤ γ) (h₁ : γ < 1)
    (π : StochasticPolicy Unit Bool) (s₀ s : Unit) :
    occupancy bandit_stochastic h₀ h₁ π s₀ s = 1 := by
  cases s
  simpa using sum_occupancy bandit_stochastic h₀ h₁ π s₀

-- At zero the success probability is 1/2 and its derivative is 1/4. With discount 1/2,
-- the stationary bandit repeats the reward, so the derivative of the total value is 1/2.
example (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    HasDerivAt (fun t => policyObjective bandit_stochastic h₀ h₁ (fun _ => 1) (coinPolicy t))
      (1 / 2) 0 := by
  have h := (hasFDerivAt_policyObjective bandit_stochastic h₀ h₁ (fun _ => 1) coin_deriv).hasDerivAt
  simp only [halfQ h₀ h₁] at h
  norm_num [unit_occupancy, sum_apply, smul_apply, Fintype.sum_bool, D,
    ContinuousLinearMap.toSpanSingleton_apply] at h ⊢
  exact h

-- The score form gives the same derivative, using both log-probability derivatives.
example (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    HasDerivAt (fun t => policyObjective bandit_stochastic h₀ h₁ (fun _ => 1) (coinPolicy t))
      (1 / 2) 0 := by
  have hlog (s : Unit) (a : Bool) := ((coin_deriv s a).log (coin_positive s a).ne').fderiv
  have h := (hasFDerivAt_policyObjective_log bandit_stochastic h₀ h₁ (fun _ => 1)
    coin_deriv coin_positive).hasDerivAt
  simp_rw [hlog, halfQ h₀ h₁] at h
  norm_num [unit_occupancy, sum_apply, smul_apply, Fintype.sum_bool, D,
    ContinuousLinearMap.toSpanSingleton_apply, coin_prob, Real.sigmoid_zero] at h ⊢
  exact h

-- The probability theorem does not need full support. This deterministic policy assigns zero
-- probability to `true` but remains in the domain of the derivative formula.
example (h₀ : (0 : ℝ) ≤ 1 / 2) (h₁ : (1 / 2 : ℝ) < 1) :
    HasFDerivAt (fun _ : ℝ => policyObjective bandit_stochastic h₀ h₁ (fun _ => 1)
      (ofDet fun _ => false)) (0 : ℝ →L[ℝ] ℝ) 0 := by
  let π : StochasticPolicy Unit Bool := ofDet fun _ => false
  simpa using hasFDerivAt_policyObjective bandit_stochastic h₀ h₁ (fun _ => 1)
    (π := fun _ : ℝ => π) (D := fun _ _ => 0) (x := 0)
    (fun s a => hasFDerivAt_const (c := π.prob s a) (0 : ℝ))

end CSLibExtTest.Algorithms.Lean.MDP.PolicyGradient
