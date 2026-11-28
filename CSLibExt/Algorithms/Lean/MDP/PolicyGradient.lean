/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PerformanceDifference
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The policy gradient theorem for stationary stochastic policies -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Asymptotics Filter Topology StochasticPolicy

variable {S A E : Type*} [Fintype S] [DecidableEq S] [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {M : MDP S A ℝ} {γ : ℝ}

/-- The discounted policy value averaged against the initial state weights `μ`. -/
noncomputable def policyObjective (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (π : StochasticPolicy S A) : ℝ :=
  ∑ s₀, μ s₀ * stochValue M γ hM hγ0 hγ1 π s₀

-- A continuous factor need not be differentiable if it multiplies a function that vanishes
-- at the base point: holding that factor fixed changes the product by o(‖y - x‖).
private theorem hasFDerivAt_mul_of_eq_zero {g r : E → ℝ} {r' : E →L[ℝ] ℝ} {x : E}
    (hg : ContinuousAt g x) (hr : HasFDerivAt r r' x) (hr0 : r x = 0) :
    HasFDerivAt (fun y => g y * r y) (g x • r') x := by
  have hg0 : (fun y => g y - g x) =o[𝓝 x] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by
      simpa only [sub_self] using hg.tendsto.sub (tendsto_const_nhds (x := g x)))
  have hrO : r =O[𝓝 x] (fun y => ‖y - x‖) := by
    simpa only [hr0, sub_zero] using hr.isBigO_sub.norm_right
  have he : (fun y => (g y - g x) * r y) =o[𝓝 x] (fun y => y - x) :=
    (by simpa only [one_mul] using hg0.mul_isBigO hrO :
      (fun y => (g y - g x) * r y) =o[𝓝 x] (fun y => ‖y - x‖)).of_norm_right
  rw [hasFDerivAt_iff_isLittleO]
  refine (he.add (hr.const_mul (g x)).isLittleO).congr_left fun y => ?_
  simp only [hr0, mul_zero]
  ring

omit [Fintype S] [DecidableEq S] in
private theorem sum_policyProb_fderiv_eq_zero {π : E → StochasticPolicy S A} {x : E}
    {D : S → A → E →L[ℝ] ℝ}
    (hD : ∀ s a, HasFDerivAt (fun t => (π t).prob s a) (D s a) x) (s : S) :
    ∑ a, D s a = 0 := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => hD s a
  simp only [StochasticPolicy.sum_prob] at h
  rw [← h.fderiv]
  exact (hasFDerivAt_const (c := (1 : ℝ)) x).fderiv

/-- **Policy gradient theorem (probability derivative form).** For a finite discounted MDP,
if the coordinates of the stationary policy `π` have Fréchet derivatives `D` at `x`, the
objective's derivative is `(1 - γ)⁻¹` times the discounted occupancy-weighted sum of
`Q^π(s,a) • D(s,a)`. No positivity of the action probabilities is required. Initial weights
may be arbitrary; for a probability vector they give the normalized discounted occupancy.
The hypotheses concern a single point; a policy class on an open set can be extended outside
it without affecting the local derivatives.

Source: Sutton, McAllester, Singh and Mansour, *Policy Gradient Methods for Reinforcement
Learning with Function Approximation*, NeurIPS 1999, Theorem 1 (discounted start-state form). -/
theorem hasFDerivAt_policyObjective (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) {π : E → StochasticPolicy S A} {x : E} {D : S → A → E →L[ℝ] ℝ}
    (hD : ∀ s a, HasFDerivAt (fun t => (π t).prob s a) (D s a) x) :
    HasFDerivAt (fun t => policyObjective hM hγ0 hγ1 μ (π t))
      ((1 - γ)⁻¹ • ∑ s, (∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (π x) s₀ s) •
        ∑ a, stochQValue hM hγ0 hγ1 (π x) s a • D s a) x := by
  let g (s : S) (t : E) := ∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (π t) s₀ s
  let r (s : S) (t : E) := ∑ a, (π t).prob s a * advantage hM hγ0 hγ1 (π x) s a
  let r' (s : S) : E →L[ℝ] ℝ := ∑ a, advantage hM hγ0 hγ1 (π x) s a • D s a
  have hg (s : S) : ContinuousAt (g s) x := by
    unfold ContinuousAt g
    exact tendsto_finsetSum _ fun s₀ _ => (tendsto_occupancy_of_tendsto hM hγ0 hγ1
      (fun s a => (hD s a).continuousAt.tendsto) s₀ s).const_mul (μ s₀)
  have hr (s : S) : HasFDerivAt (r s) (r' s) x :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun a _ =>
      (hD s a).mul_const (advantage hM hγ0 hγ1 (π x) s a)
  have hr' (s : S) : r' s = ∑ a, stochQValue hM hγ0 hγ1 (π x) s a • D s a := by
    ext v
    have hzero := congrArg (fun L : E →L[ℝ] ℝ => L v) (sum_policyProb_fderiv_eq_zero hD s)
    simp only [sum_apply, zero_apply] at hzero
    simp only [r', sum_apply, smul_apply, smul_eq_mul,
      advantage, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun s _ =>
    hasFDerivAt_mul_of_eq_zero (hg s) (hr s)
      (sum_prob_mul_advantage hM hγ0 hγ1 (π x) s)).const_mul ((1 - γ)⁻¹)
  rw [← hasFDerivAt_sub_const_iff (policyObjective hM hγ0 hγ1 μ (π x))]
  simp only [hr'] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t =>
    performance_difference_initial hM hγ0 hγ1 (π x) (π t) μ)

/-- **Policy gradient theorem (log-score form).** At a parameter with positive action
probabilities, rewrite the probability derivatives as the probabilities times the derivatives
of their logarithms. The result is the occupancy- and policy-weighted average of the log-score
weighted by the action value, scaled by `(1 - γ)⁻¹`. -/
theorem hasFDerivAt_policyObjective_log (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) {π : E → StochasticPolicy S A} {x : E} {D : S → A → E →L[ℝ] ℝ}
    (hD : ∀ s a, HasFDerivAt (fun t => (π t).prob s a) (D s a) x)
    (hpos : ∀ s a, 0 < (π x).prob s a) :
    HasFDerivAt (fun t => policyObjective hM hγ0 hγ1 μ (π t))
      ((1 - γ)⁻¹ • ∑ s, (∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 (π x) s₀ s) •
        ∑ a, ((π x).prob s a * stochQValue hM hγ0 hγ1 (π x) s a) •
          fderiv ℝ (fun t => Real.log ((π t).prob s a)) x) x := by
  have h (s : S) (a : A) := ((hD s a).log (hpos s a).ne').fderiv
  have hs (s : S) (a : A) : (π x).prob s a •
      fderiv ℝ (fun t => Real.log ((π t).prob s a)) x = D s a := by
    rw [h, smul_smul, mul_inv_cancel₀ (hpos s a).ne', one_smul]
  simp only [mul_comm ((π x).prob _ _), ← smul_smul, hs]
  exact hasFDerivAt_policyObjective hM hγ0 hγ1 μ hD

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
