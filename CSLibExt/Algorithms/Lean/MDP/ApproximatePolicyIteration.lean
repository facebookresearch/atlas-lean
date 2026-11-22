/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PolicyIteration
public import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Error bounds for approximate policy iteration

Approximate policy iteration replaces the exact evaluation of the current policy `μₖ` by an
estimate `Jₖ` with sup-norm error at most `δ`, and takes for `μₖ₊₁` a policy greedy with respect to
`Jₖ` (`policyBellman M γ μₖ₊₁ Jₖ = bellman M γ Jₖ`, i.e. `T_{μₖ₊₁} Jₖ = T Jₖ`). Over the setting of
`ValueIteration.lean` (finite states and actions, stochastic transitions, real rewards,
`0 ≤ γ < 1`; rewards are maximized, so `V^μ ≤ V*`), the results are those of
D. P. Bertsekas, *Approximate policy iteration: a survey and some new methods*, J. Control Theory
Appl. 9(3) (2011), 310–335, Section 3:

* `optimalValue_sub_policyValue_le_of_greedy`: if the method stops at `μ̄`, that is, `μ̄` is greedy
  for a `δ`-accurate estimate `J̄` of its own value, then `0 ≤ V*(s) - V^μ̄(s) ≤ 2 γ δ / (1 - γ)`
  in every state (Eq. (43) of the survey, with the survey's proof).
* `policyValue_sub_policyValue_succ_le`: along the method, a step never loses more than
  `2 γ δ / (1 - γ)` in any state.
* `optimalValue_sub_policyValue_approxPI_le`: in every state,
  `V*(s) - V^{μₖ}(s) ≤ γ ^ k ‖V* - V^{μ₀}‖∞ + 2 γ δ / (1 - γ) ^ 2`, hence
  `limsup_dist_optimalValue_policyValue_le`:
  `limsup_{k → ∞} ‖V* - V^{μₖ}‖∞ ≤ 2 γ δ / (1 - γ) ^ 2` (Eq. (42) of the survey).

With `δ = 0` the hypotheses describe exact policy iteration (`improve` of `PolicyIteration.lean`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] {M : MDP S A ℝ} {γ : ℝ}

omit [Fintype A] [Nonempty A] in
/-- **One-sided contraction of a policy's Bellman operator**: for a stochastic MDP and `γ ≥ 0`, if
`V s' - W s' ≤ m` for every state `s'`, then
`policyBellman M γ π V s - policyBellman M γ π W s ≤ γ * m` for every state `s`. -/
theorem policyBellman_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : S → A) {V W : S → ℝ} {m : ℝ}
    (h : ∀ s', V s' - W s' ≤ m) (s : S) :
    policyBellman M γ π V s - policyBellman M γ π W s ≤ γ * m := by
  have e : policyBellman M γ π V s - policyBellman M γ π W s =
      γ * ∑ s', M.prob s (π s) s' * (V s' - W s') := by
    simp only [policyBellman, qValue, mul_sub, Finset.sum_sub_distrib]; ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  calc ∑ s', M.prob s (π s) s' * (V s' - W s') ≤ ∑ s', M.prob s (π s) s' * m :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') (hM.1 s (π s) s')
    _ = m := by rw [← Finset.sum_mul, hM.2 s (π s), one_mul]

variable (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hM hγ0 hγ1

/-- The key inequality of approximate policy improvement: if `μ'` is greedy for an estimate `J`
with `|J - V^μ| ≤ δ`, then `T V^μ ≤ T_{μ'} V^μ + 2 γ δ` pointwise. -/
private theorem bellman_le_policyBellman_add {μ μ' : S → A} {J : S → ℝ} {δ : ℝ}
    (hJ : ∀ s, |J s - policyValue M γ hM hγ0 hγ1 μ s| ≤ δ)
    (hμ' : policyBellman M γ μ' J = bellman M γ J) (s : S) :
    bellman M γ (policyValue M γ hM hγ0 hγ1 μ) s ≤
      policyBellman M γ μ' (policyValue M γ hM hγ0 hγ1 μ) s + 2 * γ * δ := by
  have h1 := abs_le.1 (abs_bellman_sub_le hM hγ0 hJ s)
  have h2 := abs_le.1 (abs_policyBellman_sub_le hM hγ0 μ' hJ s)
  have h3 := congrFun hμ' s
  linarith [h1.1, h2.2]

/-- **Error bound when approximate policy iteration stops** (Bertsekas 2011, Eq. (43)): if
`|J̄ s - V^μ̄ s| ≤ δ` for every state and `μ̄` is greedy for `J̄` (`T_μ̄ J̄ = T J̄`), then
`0 ≤ V*(s) - V^μ̄(s) ≤ 2 γ δ / (1 - γ)` for every state `s`. -/
theorem optimalValue_sub_policyValue_le_of_greedy {μ : S → A} {J : S → ℝ} {δ : ℝ}
    (hJ : ∀ s, |J s - policyValue M γ hM hγ0 hγ1 μ s| ≤ δ)
    (hμ : policyBellman M γ μ J = bellman M γ J) (s : S) :
    0 ≤ optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 μ s ∧
      optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 μ s ≤
        2 * γ * δ / (1 - γ) := by
  set Vs := optimalValue M γ hM hγ0 hγ1
  set V := policyValue M γ hM hγ0 hγ1 μ
  have hge : ∀ s, 0 ≤ Vs s - V s := fun s =>
    sub_nonneg.2 (policyValue_le_optimalValue hM hγ0 hγ1 μ s)
  refine ⟨hge s, ?_⟩
  have h1γ : 0 < 1 - γ := by linarith
  set e := dist Vs V
  have he : ∀ s, |Vs s - V s| ≤ e := fun s => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist Vs V s
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hJ s)
  -- `V* - V^μ̄ ≤ γ e + 2 γ δ` pointwise
  have hpt : ∀ s, Vs s - V s ≤ γ * e + 2 * γ * δ := by
    intro s
    have h1 := (abs_le.1 (abs_bellman_sub_le hM hγ0 he s)).2
    have h2 := bellman_le_policyBellman_add hM hγ0 hγ1 hJ hμ s
    have h3 : bellman M γ Vs s = Vs s := congrFun (bellman_optimalValue hM hγ0 hγ1) s
    have h4 : policyBellman M γ μ V s = V s := congrFun (policyBellman_policyValue hM hγ0 hγ1 μ) s
    linarith
  have hdist : e ≤ γ * e + 2 * γ * δ := by
    refine (dist_pi_le_iff (by positivity)).2 fun s => ?_
    rw [Real.dist_eq, abs_of_nonneg (hge s)]
    exact hpt s
  calc Vs s - V s ≤ e := (le_abs_self _).trans (he s)
    _ ≤ 2 * γ * δ / (1 - γ) := by rw [le_div_iff₀ h1γ]; linarith

/-- **A step of approximate policy iteration loses at most `2 γ δ / (1 - γ)`**: if
`|J s - V^μ s| ≤ δ` for every state and `μ'` is greedy for `J`, then
`V^μ(s) - V^μ'(s) ≤ 2 γ δ / (1 - γ)` for every state `s`. -/
theorem policyValue_sub_policyValue_succ_le {μ μ' : S → A} {J : S → ℝ} {δ : ℝ}
    (hJ : ∀ s, |J s - policyValue M γ hM hγ0 hγ1 μ s| ≤ δ)
    (hμ' : policyBellman M γ μ' J = bellman M γ J) (s : S) :
    policyValue M γ hM hγ0 hγ1 μ s - policyValue M γ hM hγ0 hγ1 μ' s ≤ 2 * γ * δ / (1 - γ) := by
  have : Nonempty S := ⟨s⟩
  set V := policyValue M γ hM hγ0 hγ1 μ
  set V' := policyValue M γ hM hγ0 hγ1 μ'
  have h1γ : 0 < 1 - γ := by linarith
  set D : S → ℝ := fun s => V s - V' s
  set m := Finset.univ.sup' Finset.univ_nonempty D
  have hD : ∀ s, D s ≤ m := fun s => Finset.le_sup' D (Finset.mem_univ s)
  have hpt : ∀ s, D s ≤ 2 * γ * δ + γ * m := by
    intro s
    have h1 := bellman_le_policyBellman_add hM hγ0 hγ1 hJ hμ' s
    have h2 := policyBellman_sub_le hM hγ0 μ' hD s
    have h3 : policyBellman M γ μ V s ≤ bellman M γ V s := policyBellman_le_bellman μ V s
    have h4 : policyBellman M γ μ V s = V s := congrFun (policyBellman_policyValue hM hγ0 hγ1 μ) s
    have h5 : policyBellman M γ μ' V' s = V' s :=
      congrFun (policyBellman_policyValue hM hγ0 hγ1 μ') s
    simp only [D] at h2 ⊢
    linarith
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty D
  have hm : m ≤ 2 * γ * δ / (1 - γ) := by
    rw [le_div_iff₀ h1γ]
    have := hpt s₀
    rw [← hs₀] at this
    linarith
  exact (hD s).trans hm

/-- **Error bound for approximate policy iteration** (Bertsekas 2011, Eq. (42), in non-asymptotic
form): let `μ : ℕ → S → A` and `J : ℕ → S → ℝ` satisfy `|J k s - V^{μ k} s| ≤ δ` for all `k` and
`s`, with `μ (k + 1)` greedy for `J k`. Then for all `k` and `s`,
`V*(s) - V^{μ k}(s) ≤ γ ^ k * ‖V* - V^{μ 0}‖∞ + 2 γ δ / (1 - γ) ^ 2`. -/
theorem optimalValue_sub_policyValue_approxPI_le {μ : ℕ → S → A} {J : ℕ → S → ℝ} {δ : ℝ}
    (hJ : ∀ k s, |J k s - policyValue M γ hM hγ0 hγ1 (μ k) s| ≤ δ)
    (hμ : ∀ k, policyBellman M γ (μ (k + 1)) (J k) = bellman M γ (J k)) (k : ℕ) (s : S) :
    optimalValue M γ hM hγ0 hγ1 s - policyValue M γ hM hγ0 hγ1 (μ k) s ≤
      γ ^ k * dist (optimalValue M γ hM hγ0 hγ1) (policyValue M γ hM hγ0 hγ1 (μ 0)) +
        2 * γ * δ / (1 - γ) ^ 2 := by
  have : Nonempty S := ⟨s⟩
  set Vs := optimalValue M γ hM hγ0 hγ1
  set V : ℕ → S → ℝ := fun k => policyValue M γ hM hγ0 hγ1 (μ k)
  have h1γ : 0 < 1 - γ := by linarith
  set β := 2 * γ * δ / (1 - γ)
  have hβ : 2 * γ * δ + γ * β = β := by simp only [β]; field_simp; ring
  set ε : ℕ → ℝ := fun k => Finset.univ.sup' Finset.univ_nonempty fun s => Vs s - V k s
  have hε : ∀ k s, Vs s - V k s ≤ ε k := fun k s =>
    Finset.le_sup' (fun s => Vs s - V k s) (Finset.mem_univ s)
  have hge : ∀ k s, 0 ≤ Vs s - V k s := fun k s =>
    sub_nonneg.2 (policyValue_le_optimalValue hM hγ0 hγ1 (μ k) s)
  -- one step: `ε (k + 1) ≤ γ ε k + β`
  have hstep : ∀ k, ε (k + 1) ≤ γ * ε k + β := by
    intro k
    have hpt : ∀ s, Vs s - V (k + 1) s ≤ γ * ε k + β := by
      intro s
      have habs : ∀ s, |Vs s - V k s| ≤ ε k := fun s => by
        rw [abs_of_nonneg (hge k s)]; exact hε k s
      have h1 := (abs_le.1 (abs_bellman_sub_le hM hγ0 habs s)).2
      have h2 := bellman_le_policyBellman_add hM hγ0 hγ1 (hJ k) (hμ k) s
      have hloss : ∀ s, V k s - V (k + 1) s ≤ β := fun s =>
        policyValue_sub_policyValue_succ_le hM hγ0 hγ1 (hJ k) (hμ k) s
      have h3 := policyBellman_sub_le hM hγ0 (μ (k + 1)) hloss s
      have h4 : bellman M γ Vs s = Vs s := congrFun (bellman_optimalValue hM hγ0 hγ1) s
      have h5 : policyBellman M γ (μ (k + 1)) (V (k + 1)) s = V (k + 1) s :=
        congrFun (policyBellman_policyValue hM hγ0 hγ1 (μ (k + 1))) s
      linarith
    obtain ⟨s₀, -, hs₀⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty fun s => Vs s - V (k + 1) s
    simp only [ε]
    rw [hs₀]
    exact hpt s₀
  -- unrolled: `ε k ≤ γ ^ k ε 0 + β / (1 - γ)`
  have hunroll : ∀ k, ε k ≤ γ ^ k * ε 0 + β / (1 - γ) := by
    intro k
    induction k with
    | zero =>
        have : 0 ≤ β / (1 - γ) := by
          have hδ : 0 ≤ δ := (abs_nonneg _).trans (hJ 0 s)
          positivity
        simp only [pow_zero, one_mul]; linarith
    | succ k ih =>
        have hβ' : γ * (β / (1 - γ)) + β = β / (1 - γ) := by field_simp; ring
        calc ε (k + 1) ≤ γ * ε k + β := hstep k
          _ ≤ γ * (γ ^ k * ε 0 + β / (1 - γ)) + β := by gcongr
          _ = γ ^ (k + 1) * ε 0 + β / (1 - γ) := by rw [pow_succ]; linarith [hβ']
  have hε0 : ε 0 ≤ dist Vs (V 0) := by
    obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun s => Vs s - V 0 s
    simp only [ε]
    rw [hs₀, ← abs_of_nonneg (hge 0 s₀), ← Real.dist_eq]
    exact dist_le_pi_dist Vs (V 0) s₀
  have hβ2 : β / (1 - γ) = 2 * γ * δ / (1 - γ) ^ 2 := by simp only [β]; field_simp
  calc Vs s - V k s ≤ ε k := hε k s
    _ ≤ γ ^ k * ε 0 + β / (1 - γ) := hunroll k
    _ ≤ γ ^ k * dist Vs (V 0) + β / (1 - γ) := by gcongr
    _ = _ := by rw [hβ2]

/-- **Asymptotic error bound for approximate policy iteration** (Bertsekas 2011, Eq. (42)): under
the hypotheses of `optimalValue_sub_policyValue_approxPI_le`, with at least one state,
`limsup_{k → ∞} ‖V* - V^{μ k}‖∞ ≤ 2 γ δ / (1 - γ) ^ 2`. -/
theorem limsup_dist_optimalValue_policyValue_le [Nonempty S] {μ : ℕ → S → A} {J : ℕ → S → ℝ}
    {δ : ℝ} (hJ : ∀ k s, |J k s - policyValue M γ hM hγ0 hγ1 (μ k) s| ≤ δ)
    (hμ : ∀ k, policyBellman M γ (μ (k + 1)) (J k) = bellman M γ (J k)) :
    limsup (fun k => dist (optimalValue M γ hM hγ0 hγ1) (policyValue M γ hM hγ0 hγ1 (μ k)))
      atTop ≤ 2 * γ * δ / (1 - γ) ^ 2 := by
  set Vs := optimalValue M γ hM hγ0 hγ1
  set d0 := dist Vs (policyValue M γ hM hγ0 hγ1 (μ 0))
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hJ 0 (Classical.arbitrary S))
  have h1γ : 0 < 1 - γ := by linarith
  -- the explicit bound, in sup norm
  have hk : ∀ k, dist Vs (policyValue M γ hM hγ0 hγ1 (μ k)) ≤
      γ ^ k * d0 + 2 * γ * δ / (1 - γ) ^ 2 := by
    intro k
    refine (dist_pi_le_iff (by positivity)).2 fun s => ?_
    rw [Real.dist_eq, abs_of_nonneg
      (sub_nonneg.2 (policyValue_le_optimalValue hM hγ0 hγ1 (μ k) s))]
    exact optimalValue_sub_policyValue_approxPI_le hM hγ0 hγ1 hJ hμ k s
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun k => dist Vs (policyValue M γ hM hγ0 hγ1 (μ k))) :=
    isCoboundedUnder_le_of_le atTop fun k => dist_nonneg
  refine le_of_forall_pos_le_add fun ε hε => limsup_le_of_le hcob ?_
  have ht : Tendsto (fun k => γ ^ k * d0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const d0
  filter_upwards [(ht.eventually (gt_mem_nhds hε))] with k hk'
  linarith [hk k]

end Cslib.Algorithms.Lean.MarkovDecision
