/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.GreedyPolicyBound
public import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Approximate value iteration: sup-norm policy loss

For a stochastic finite discounted MDP, a sequence of value estimates with uniform one-step
Bellman error at most `ε` stays within a decaying initial error plus the error accumulated by
contraction. The greedy policy loss has limit superior at most `2 γ ε / (1 - γ)^2`. This does
not require the estimates or the policies to converge, or a fixed approximation operator.

The contraction recurrence follows Rémi Munos, *Performance Bounds in Lp-norm for Approximate
Value Iteration*, SIAM Journal on Control and Optimization 46(2), 541–561 (2007), §2, equations
(2.1)–(2.3). Shifting the recurrence before applying Mathlib's discrete Grönwall lemma gives
the finite-time refinement.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] {M : MDP S A ℝ} {γ : ℝ}
  (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- **Finite-time approximate value error.** If successive value estimates differ from the
Bellman update by at most `ε` in sup norm, after `n` updates the initial error is reduced by
`γ ^ n`, and the accumulated error is at most `(1 - γ ^ n) * (ε / (1 - γ))`. -/
theorem dist_optimalValue_approximateValueIteration_le {V : ℕ → S → ℝ} {ε : ℝ}
    (hstep : ∀ n, dist (bellman M γ (V n)) (V (n + 1)) ≤ ε) (n : ℕ) :
    dist (optimalValue M γ hM hγ0 hγ1) (V n) ≤
      γ ^ n * dist (optimalValue M γ hM hγ0 hγ1) (V 0) + (1 - γ ^ n) * (ε / (1 - γ)) := by
  let Vstar := optimalValue M γ hM hγ0 hγ1
  let b := ε / (1 - γ)
  have hb : γ * b + ε = b := by
    dsimp [b]
    field_simp [ne_of_gt (sub_pos.mpr hγ1)]
    ring
  have hrec (k : ℕ) : dist Vstar (V (k + 1)) ≤ γ * dist Vstar (V k) + ε := by
    have hT := (bellman_contracting hM hγ0 hγ1).dist_le_mul Vstar (V k)
    rw [Real.coe_toNNReal γ hγ0, show bellman M γ Vstar = Vstar from
      bellman_optimalValue hM hγ0 hγ1] at hT
    exact (dist_triangle Vstar (bellman M γ (V k)) (V (k + 1))).trans
      (add_le_add hT (hstep k))
  have hshift (k : ℕ) (_ : 0 ≤ k) :
      dist Vstar (V (k + 1)) - b ≤ γ * (dist Vstar (V k) - b) + 0 := by
    nlinarith only [hrec k, hb]
  have h := discrete_gronwall_prod_general (n₀ := 0)
    (u := fun k => dist Vstar (V k) - b) (c := fun _ => γ) (b := fun _ => 0)
    hshift (fun _ _ => hγ0) (Nat.zero_le n)
  simp only [Finset.prod_const, Nat.card_Ico, Nat.sub_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at h
  change dist Vstar (V n) ≤ γ ^ n * dist Vstar (V 0) + (1 - γ ^ n) * b
  linarith only [h]

/-- **Finite-time approximate value-iteration policy loss.** Any policy greedy for the `n`th
estimate has sup-norm loss at most `2 γ / (1 - γ)` times the finite-time value-error bound. -/
theorem dist_optimalValue_policyValue_approximateValueIteration_le [Nonempty S]
    {V : ℕ → S → ℝ} {π : ℕ → S → A} {ε : ℝ}
    (hstep : ∀ n, dist (bellman M γ (V n)) (V (n + 1)) ≤ ε)
    (hgreedy : ∀ n, policyBellman M γ (π n) (V n) = bellman M γ (V n)) (n : ℕ) :
    dist (optimalValue M γ hM hγ0 hγ1) (policyValue M γ hM hγ0 hγ1 (π n)) ≤
      2 * γ / (1 - γ) * (γ ^ n * dist (optimalValue M γ hM hγ0 hγ1) (V 0) +
        (1 - γ ^ n) * (ε / (1 - γ))) :=
  (dist_optimalValue_policyValue_le_of_greedy hM hγ0 hγ1 (V n) (π n) (hgreedy n)).trans
    (mul_le_mul_of_nonneg_left (dist_optimalValue_approximateValueIteration_le hM hγ0 hγ1 hstep n)
      (div_nonneg (mul_nonneg (by norm_num) hγ0) (sub_nonneg.mpr hγ1.le)))

/-- **Approximate value iteration policy loss** (Munos 2007, equation (2.2)). For any sequence of
approximate value estimates with Bellman step errors of sup norm at most `ε` and any sequence
of policies greedy for those estimates, the limit superior of the sup-norm policy losses is
at most `2 γ ε / (1 - γ)^2`. The hypotheses impose neither a fixed tie breaker nor convergence. -/
theorem limsup_dist_optimalValue_policyValue_approximateValueIteration_le [Nonempty S]
    {V : ℕ → S → ℝ} {π : ℕ → S → A} {ε : ℝ}
    (hstep : ∀ n, dist (bellman M γ (V n)) (V (n + 1)) ≤ ε)
    (hgreedy : ∀ n, policyBellman M γ (π n) (V n) = bellman M γ (V n)) :
    limsup (fun n => dist (optimalValue M γ hM hγ0 hγ1)
      (policyValue M γ hM hγ0 hγ1 (π n))) atTop ≤ 2 * γ * ε / (1 - γ) ^ 2 := by
  let Vstar := optimalValue M γ hM hγ0 hγ1
  let loss := fun n => dist Vstar (policyValue M γ hM hγ0 hγ1 (π n))
  let upper := fun n => 2 * γ / (1 - γ) *
    (γ ^ n * dist Vstar (V 0) + (1 - γ ^ n) * (ε / (1 - γ)))
  have hle (n : ℕ) : loss n ≤ upper n :=
    dist_optimalValue_policyValue_approximateValueIteration_le hM hγ0 hγ1 hstep hgreedy n
  have hp : Tendsto (fun n : ℕ => γ ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1
  have ht : Tendsto upper atTop (𝓝 (2 * γ * ε / (1 - γ) ^ 2)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have ht' := ((hp.mul_const (dist Vstar (V 0))).add
      ((hone.sub hp).mul_const (ε / (1 - γ)))).const_mul (2 * γ / (1 - γ))
    have hconst : 2 * γ / (1 - γ) * (ε / (1 - γ)) = 2 * γ * ε / (1 - γ) ^ 2 := by
      rw [div_mul_div_comm, pow_two]
    simpa only [upper, zero_mul, sub_zero, one_mul, zero_add, hconst] using ht'
  -- The passage from a convergent envelope to a limsup bound follows
  -- `limsup_dist_optimalValue_policyValue_le` in `ApproximatePolicyIteration.lean`.
  have hlow : IsCoboundedUnder (· ≤ ·) atTop loss :=
    isCoboundedUnder_le_of_le atTop fun _ => dist_nonneg
  refine le_of_forall_pos_le_add fun η hη => limsup_le_of_le hlow ?_
  filter_upwards [ht.eventually (gt_mem_nhds (lt_add_of_pos_right _ hη))] with n hn
  exact (hle n).trans hn.le

end Cslib.Algorithms.Lean.MarkovDecision
