/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PerformanceDifference
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Global convergence of natural policy gradient with softmax policies

The softmax policy of logits `θ : S → A → ℝ` is `π_θ(a | s) = exp θ(s, a) / ∑ b, exp θ(s, b)`
(`StochasticPolicy.softmax`). For this parameterization the natural policy gradient update
`θ ← θ + η F(θ)† ∇V^{π_θ}` (Kakade, *A Natural Policy Gradient*, NeurIPS 2001) takes the closed
form `θ_{t+1} = θ_t + η / (1 - γ) * A^{π_t}` (Agarwal, Kakade, Lee and Mahajan, *On the Theory of
Policy Gradient Methods*, JMLR 22 (2021), Lemma 5.1; AJKS Lemma 12.6): a soft policy iteration
that multiplies `π_t(a | s)` by `exp (η A^{π_t}(s, a) / (1 - γ))` and renormalizes, that is,
multiplicative weights run in every state with the advantages as gains. `npgLogits` is this
iteration from `θ_0 = 0` (the uniform policy) and `npgPolicy` its policies. The Fisher update
takes this form on the states reachable from the start distribution `ρ` (AKLM, footnote 6), up
to a state-dependent offset that the softmax ignores (AJKS Lemma 12.6); here the soft policy
iteration is applied at every state. NPG is defined here by this closed form; its derivation
from the Fisher-preconditioned gradient (AKLM Lemma 5.1) is not formalized.

Main results, for a finite stochastic MDP with `0 ≤ γ < 1` and step size `η > 0`:

* `npg_improvement`: **the improvement lower bound** (AKLM Lemma 5.2; AJKS Lemma 12.8): with
  `log Z_t(s) = lse θ_{t+1}(s) - lse θ_t(s) ≥ 0` (`lse_npgLogits_succ_sub_nonneg`),
  `V^{(t+1)}(s) - V^{(t)}(s) ≥ (1 - γ) / η * log Z_t(s) ≥ 0`, so the values increase
  (`stochValue_npgPolicy_mono`).
* `optimalValue_sub_stochValue_npgPolicy_le`: **global convergence of NPG** (AKLM Theorem 5.3;
  AJKS Theorem 12.7): if all rewards lie in `[0, 1]`, then for every `T ≥ 1` and every state `s`,
  `V*(s) - V^{(T)}(s) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`.
  Averaging over a start distribution `ρ` gives the published form
  `V^{(T)}(ρ) ≥ V*(ρ) - log |A| / (η T) - 1 / ((1 - γ)² T)`; the rate depends on neither `|S|` nor
  a distribution mismatch coefficient.

The proof is the published one: the performance difference lemma against an optimal
deterministic policy turns `V* - V^{(t)}` into a telescoping cross-entropy term plus
`log Z_t`, and the improvement lemma bounds `∑ₜ log Z_t` by the total value gain.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Real Convexity

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

/-! ## Softmax policies -/

/-- The log-partition function `lse θ s = log ∑ b, exp θ(s, b)` of the logits `θ`, a raw
log-sum-exp helper. It is the log-partition function of the softmax policy for a nonempty action
set, as in every result below; on an empty action set it would be `log 0 = 0`. -/
noncomputable def lse (θ : S → A → ℝ) (s : S) : ℝ := log (∑ b, exp (θ s b))

omit [Fintype S] [DecidableEq S] in
/-- The partition function `∑ b, exp θ(s, b)` is positive. -/
theorem sum_exp_pos (θ : S → A → ℝ) (s : S) : 0 < ∑ b, exp (θ s b) :=
  Finset.sum_pos (fun _ _ => exp_pos _) Finset.univ_nonempty

namespace StochasticPolicy

omit [Fintype S] [DecidableEq S] in
/-- The softmax policy `π_θ(a | s) = exp θ(s, a) / ∑ b, exp θ(s, b)` of the logits `θ` (AKLM,
equation (3)). -/
noncomputable def softmax (θ : S → A → ℝ) : StochasticPolicy S A :=
  fun s =>
    { weights := Finsupp.equivFunOnFinite.symm fun a => exp (θ s a) / ∑ b, exp (θ s b)
      nonneg := fun a => by
        simpa using div_nonneg (exp_pos (θ s a)).le (sum_exp_pos θ s).le
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp [← Finset.sum_div, div_self (sum_exp_pos θ s).ne'] }

omit [Fintype S] [DecidableEq S] in
/-- The softmax policy takes action `a` in state `s` with probability
`exp θ(s, a) / ∑ b, exp θ(s, b)`. -/
theorem softmax_prob (θ : S → A → ℝ) (s : S) (a : A) :
    (softmax θ).prob s a = exp (θ s a) / ∑ b, exp (θ s b) := by
  simp [softmax, prob]

omit [Fintype S] [DecidableEq S] in
/-- Softmax policies give every action positive probability. -/
theorem softmax_prob_pos (θ : S → A → ℝ) (s : S) (a : A) : 0 < (softmax θ).prob s a := by
  rw [softmax_prob]
  exact div_pos (exp_pos _) (sum_exp_pos θ s)

omit [Fintype S] [DecidableEq S] in
/-- Softmax probabilities are at most one. -/
theorem softmax_prob_le_one (θ : S → A → ℝ) (s : S) (a : A) : (softmax θ).prob s a ≤ 1 := by
  rw [softmax_prob, div_le_one (sum_exp_pos θ s)]
  exact Finset.single_le_sum (fun b _ => (exp_pos (θ s b)).le) (Finset.mem_univ a)

omit [Fintype S] [DecidableEq S] in
/-- `log π_θ(a | s) = θ(s, a) - lse θ s`. -/
theorem log_softmax_prob (θ : S → A → ℝ) (s : S) (a : A) :
    log ((softmax θ).prob s a) = θ s a - lse θ s := by
  rw [softmax_prob, log_div (exp_pos _).ne' (sum_exp_pos θ s).ne', log_exp, lse]

omit [Fintype S] [DecidableEq S] in
/-- The softmax policy of the zero logits is uniform. -/
theorem softmax_zero_prob (s : S) (a : A) :
    (softmax (0 : S → A → ℝ)).prob s a = 1 / Fintype.card A := by
  simp [softmax_prob]

end StochasticPolicy

open StochasticPolicy

omit [Fintype S] [DecidableEq S] in
/-- **Convexity of the log-partition function** (Jensen's inequality for `exp`):
`lse θ' s - lse θ s ≥ ∑ b, π_θ(b | s) (θ'(s, b) - θ(s, b))`. -/
theorem sum_softmax_prob_mul_sub_le_lse_sub (θ θ' : S → A → ℝ) (s : S) :
    ∑ b, (softmax θ).prob s b * (θ' s b - θ s b) ≤ lse θ' s - lse θ s := by
  set Z := ∑ b, exp (θ s b)
  have hZ : 0 < Z := sum_exp_pos θ s
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun b => (softmax θ).prob s b)
    (p := fun b => θ' s b - θ s b) (fun b _ => (softmax θ).prob_nonneg s b)
    ((softmax θ).sum_prob s) (fun b _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hsum : ∑ b, (softmax θ).prob s b * exp (θ' s b - θ s b) = (∑ b, exp (θ' s b)) / Z := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [softmax_prob, div_mul_eq_mul_div, ← exp_add, add_sub_cancel]
  rw [hsum] at hJ
  have hpos : 0 < (∑ b, exp (θ' s b)) / Z := div_pos (sum_exp_pos θ' s) hZ
  have := (le_log_iff_exp_le hpos).2 hJ
  rwa [log_div (sum_exp_pos θ' s).ne' hZ.ne'] at this

omit [Fintype S] [DecidableEq S] in
/-- **Gibbs' inequality** for softmax policies: the relative entropy
`∑ a, π_θ'(a | s) (log π_θ'(a | s) - log π_θ(a | s))` is nonnegative. -/
theorem sum_softmax_mul_log_sub_nonneg (θ θ' : S → A → ℝ) (s : S) :
    0 ≤ ∑ a, (softmax θ').prob s a *
      (log ((softmax θ').prob s a) - log ((softmax θ).prob s a)) := by
  have h : ∀ a, (softmax θ').prob s a * (log ((softmax θ).prob s a) -
      log ((softmax θ').prob s a)) ≤ (softmax θ).prob s a - (softmax θ').prob s a := by
    intro a
    have hp := softmax_prob_pos θ' s a
    have hq := softmax_prob_pos θ s a
    rw [← log_div hq.ne' hp.ne']
    have := log_le_sub_one_of_pos (div_pos hq hp)
    calc (softmax θ').prob s a * log ((softmax θ).prob s a / (softmax θ').prob s a)
        ≤ (softmax θ').prob s a * ((softmax θ).prob s a / (softmax θ').prob s a - 1) :=
          mul_le_mul_of_nonneg_left this hp.le
      _ = (softmax θ).prob s a - (softmax θ').prob s a := by field_simp
  have hs := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => h a
  rw [Finset.sum_sub_distrib, (softmax θ).sum_prob, (softmax θ').sum_prob, sub_self] at hs
  have : ∑ a, (softmax θ').prob s a * (log ((softmax θ').prob s a) -
      log ((softmax θ).prob s a)) = -∑ a, (softmax θ').prob s a *
        (log ((softmax θ).prob s a) - log ((softmax θ').prob s a)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  linarith

/-! ## The natural policy gradient iteration -/

variable {M : MDP S A ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- The logits of natural policy gradient with softmax policies and step size `η`, from
`θ_0 = 0`: `θ_{t+1} = θ_t + η / (1 - γ) * A^{π_{θ_t}}` (AKLM Lemma 5.1; AJKS Lemma 12.6). The
Fisher update has this form on the states reachable from the start distribution (AKLM,
footnote 6), up to a state-dependent offset; here it is applied at every state. -/
noncomputable def npgLogits (η : ℝ) : ℕ → S → A → ℝ
  | 0 => 0
  | t + 1 => fun s a =>
      npgLogits η t s a + η / (1 - γ) * advantage hM hγ0 hγ1 (softmax (npgLogits η t)) s a

/-- The policy `π_t = π_{θ_t}` after `t` steps of natural policy gradient. -/
noncomputable def npgPolicy (η : ℝ) (t : ℕ) : StochasticPolicy S A :=
  softmax (npgLogits hM hγ0 hγ1 η t)

include hM hγ0 hγ1

/-- One NPG step adds `η / (1 - γ)` times the current advantage to the logits. -/
theorem npgLogits_succ (η : ℝ) (t : ℕ) (s : S) (a : A) :
    npgLogits hM hγ0 hγ1 η (t + 1) s a = npgLogits hM hγ0 hγ1 η t s a +
      η / (1 - γ) * advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s a := rfl

/-- `log Z_t(s) = lse θ_{t+1}(s) - lse θ_t(s)` is nonnegative. -/
theorem lse_npgLogits_succ_sub_nonneg (η : ℝ) (t : ℕ) (s : S) :
    0 ≤ lse (npgLogits hM hγ0 hγ1 η (t + 1)) s - lse (npgLogits hM hγ0 hγ1 η t) s := by
  have h := sum_softmax_prob_mul_sub_le_lse_sub (npgLogits hM hγ0 hγ1 η t)
    (npgLogits hM hγ0 hγ1 η (t + 1)) s
  have h0 := sum_prob_mul_advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s
  have : ∑ b, (softmax (npgLogits hM hγ0 hγ1 η t)).prob s b *
      (npgLogits hM hγ0 hγ1 η (t + 1) s b - npgLogits hM hγ0 hγ1 η t s b) = 0 := by
    simp_rw [npgLogits_succ, add_sub_cancel_left]
    rw [show (fun b => (softmax (npgLogits hM hγ0 hγ1 η t)).prob s b *
        (η / (1 - γ) * advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s b)) =
        fun b => η / (1 - γ) * ((npgPolicy hM hγ0 hγ1 η t).prob s b *
          advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s b) from
        funext fun b => by rw [npgPolicy]; ring]
    rw [← Finset.mul_sum, h0, mul_zero]
  linarith

/-- The step `η / (1 - γ)` times the averaged advantage of `π_{t+1}` over `π_t` is the relative
entropy of `π_{t+1}` from `π_t` plus `log Z_t`, hence at least `log Z_t`. -/
theorem lse_npgLogits_succ_sub_le (η : ℝ) (t : ℕ) (s : S) :
    lse (npgLogits hM hγ0 hγ1 η (t + 1)) s - lse (npgLogits hM hγ0 hγ1 η t) s ≤
      η / (1 - γ) * ∑ a, (npgPolicy hM hγ0 hγ1 η (t + 1)).prob s a *
        advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s a := by
  set θ := npgLogits hM hγ0 hγ1 η t
  set θ' := npgLogits hM hγ0 hγ1 η (t + 1)
  have hkl := sum_softmax_mul_log_sub_nonneg θ θ' s
  have hstep : ∀ a, η / (1 - γ) * advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s a =
      (log ((softmax θ').prob s a) - log ((softmax θ).prob s a)) + (lse θ' s - lse θ s) := by
    intro a
    rw [log_softmax_prob, log_softmax_prob]
    have := npgLogits_succ hM hγ0 hγ1 η t s a
    linarith
  rw [Finset.mul_sum]
  simp_rw [mul_left_comm (η / (1 - γ)), hstep, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  rw [npgPolicy, (softmax θ').sum_prob, one_mul]
  linarith

/-- **Improvement lower bound for NPG** (AKLM Lemma 5.2; AJKS Lemma 12.8, from a single start
state): for `η > 0`, `V^{(t+1)}(s₀) - V^{(t)}(s₀) ≥ (1 - γ) / η * log Z_t(s₀)`, where
`log Z_t = lse θ_{t+1} - lse θ_t ≥ 0`. -/
theorem npg_improvement {η : ℝ} (hη : 0 < η) (t : ℕ) (s₀ : S) :
    (1 - γ) / η * (lse (npgLogits hM hγ0 hγ1 η (t + 1)) s₀ - lse (npgLogits hM hγ0 hγ1 η t) s₀)
      ≤ stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η (t + 1)) s₀ -
        stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s₀ := by
  set p := npgPolicy hM hγ0 hγ1 η t
  set q := npgPolicy hM hγ0 hγ1 η (t + 1)
  set ℓ : S → ℝ := fun s =>
    lse (npgLogits hM hγ0 hγ1 η (t + 1)) s - lse (npgLogits hM hγ0 hγ1 η t) s
  have h1γ : 0 < 1 - γ := by linarith
  have hc : 0 < η / (1 - γ) := div_pos hη h1γ
  have hℓ0 : ∀ s, 0 ≤ ℓ s := lse_npgLogits_succ_sub_nonneg hM hγ0 hγ1 η t
  -- `ℓ s / c ≤ g s`, with `g s` the averaged advantage
  have hg : ∀ s, (1 - γ) / η * ℓ s ≤ ∑ a, q.prob s a * advantage hM hγ0 hγ1 p s a := by
    intro s
    have := lse_npgLogits_succ_sub_le hM hγ0 hγ1 η t s
    have e : (1 - γ) / η * (η / (1 - γ)) = 1 := by field_simp
    calc (1 - γ) / η * ℓ s ≤ (1 - γ) / η * (η / (1 - γ) *
          ∑ a, q.prob s a * advantage hM hγ0 hγ1 p s a) :=
          mul_le_mul_of_nonneg_left this (div_pos h1γ hη).le
      _ = _ := by rw [← mul_assoc, e, one_mul]
  rw [performance_difference hM hγ0 hγ1 p q s₀]
  have hd := one_sub_le_visitation_self (policyKernel_mem hM q) hγ0 hγ1 s₀
  calc (1 - γ) / η * ℓ s₀
      = (1 - γ)⁻¹ * ((1 - γ) * ((1 - γ) / η * ℓ s₀)) := by field_simp
    _ ≤ (1 - γ)⁻¹ * (occupancy hM hγ0 hγ1 q s₀ s₀ * ((1 - γ) / η * ℓ s₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1γ.le)
        exact mul_le_mul_of_nonneg_right hd (mul_nonneg (div_pos h1γ hη).le (hℓ0 s₀))
    _ ≤ (1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 q s₀ s * ((1 - γ) / η * ℓ s) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1γ.le)
        exact Finset.single_le_sum (f := fun s => occupancy hM hγ0 hγ1 q s₀ s *
          ((1 - γ) / η * ℓ s)) (fun s _ => mul_nonneg (occupancy_nonneg hM hγ0 hγ1 q s₀ s)
            (mul_nonneg (div_pos h1γ hη).le (hℓ0 s))) (Finset.mem_univ s₀)
    _ ≤ (1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 q s₀ s *
          ∑ a, q.prob s a * advantage hM hγ0 hγ1 p s a := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 h1γ.le)
        exact Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hg s) (occupancy_nonneg hM hγ0 hγ1 q s₀ s)

/-- The values of the NPG iterates never decrease. -/
theorem stochValue_npgPolicy_mono {η : ℝ} (hη : 0 < η) (s : S) :
    Monotone fun t => stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s := by
  refine monotone_nat_of_le_succ fun t => ?_
  have h := npg_improvement hM hγ0 hγ1 hη t s
  have h0 := lse_npgLogits_succ_sub_nonneg hM hγ0 hγ1 η t s
  have : 0 ≤ (1 - γ) / η * (lse (npgLogits hM hγ0 hγ1 η (t + 1)) s -
      lse (npgLogits hM hγ0 hγ1 η t) s) := mul_nonneg (div_pos (by linarith) hη).le h0
  linarith

/-- **Global convergence of natural policy gradient** (Agarwal, Kakade, Lee and Mahajan 2021,
Theorem 5.3; AJKS Theorem 12.7): for a finite MDP with rewards in `[0, 1]`, softmax policies,
step size `η > 0` and `θ_0 = 0`, after `T ≥ 1` iterations, for every state `s₀`,
`V*(s₀) - V^{(T)}(s₀) ≤ log |A| / (η T) + 1 / ((1 - γ)² T)`. -/
theorem optimalValue_sub_stochValue_npgPolicy_le
    (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) {η : ℝ} (hη : 0 < η) {T : ℕ}
    (hT : 0 < T) (s₀ : S) :
    optimalValue M γ hM hγ0 hγ1 s₀ - stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η T) s₀ ≤
      log (Fintype.card A) / (η * T) + 1 / ((1 - γ) ^ 2 * T) := by
  have h1γ : 0 < 1 - γ := by linarith
  set V := fun t => stochValue M γ hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t)
  set Vstar := optimalValue M γ hM hγ0 hγ1
  -- an optimal deterministic policy, as a stochastic one
  set πs : StochasticPolicy S A := ofDet (greedy M γ Vstar)
  have hπs : stochValue M γ hM hγ0 hγ1 πs = Vstar := by
    rw [stochValue_ofDet, policyValue_greedy]
  set d := fun s => occupancy hM hγ0 hγ1 πs s₀ s
  have hd0 : ∀ s, 0 ≤ d s := fun s => occupancy_nonneg hM hγ0 hγ1 πs s₀ s
  have hd1 : ∑ s, d s = 1 := sum_occupancy hM hγ0 hγ1 πs s₀
  -- cross-entropy potential `Φ_t(s) = -∑ a, π*(a | s) log π_t(a | s)`
  set Φ : ℕ → S → ℝ := fun t s =>
    -∑ a, πs.prob s a * log ((npgPolicy hM hγ0 hγ1 η t).prob s a)
  set ℓ : ℕ → S → ℝ := fun t s =>
    lse (npgLogits hM hγ0 hγ1 η (t + 1)) s - lse (npgLogits hM hγ0 hγ1 η t) s
  -- one step: `V* - V_t = (1/η) ∑ d (Φ_t - Φ_{t+1} + ℓ_t)`
  have hstep : ∀ t, Vstar s₀ - V t s₀ = 1 / η * ∑ s, d s * (Φ t s - Φ (t + 1) s + ℓ t s) := by
    intro t
    have hpd := performance_difference hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) πs s₀
    rw [hπs] at hpd
    simp only [V]
    rw [hpd]
    have hA : ∀ s, ∑ a, πs.prob s a * advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s a =
        (1 - γ) / η * (Φ t s - Φ (t + 1) s + ℓ t s) := by
      intro s
      have hlog : ∀ a, advantage hM hγ0 hγ1 (npgPolicy hM hγ0 hγ1 η t) s a =
          (1 - γ) / η * (log ((npgPolicy hM hγ0 hγ1 η (t + 1)).prob s a) -
            log ((npgPolicy hM hγ0 hγ1 η t).prob s a) + ℓ t s) := by
        intro a
        simp only [npgPolicy, ℓ]
        rw [log_softmax_prob, log_softmax_prob, npgLogits_succ, npgPolicy]
        field_simp
        ring
      have hΦ : Φ t s - Φ (t + 1) s + ℓ t s = ∑ a, πs.prob s a *
          (log ((npgPolicy hM hγ0 hγ1 η (t + 1)).prob s a) -
            log ((npgPolicy hM hγ0 hγ1 η t).prob s a) + ℓ t s) := by
        simp only [Φ, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, πs.sum_prob, one_mul]
        ring
      rw [hΦ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hlog a]
      ring
    simp_rw [hA]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [d]
    field_simp
  -- `ℓ_t(s) ≤ η / (1 - γ) (V_{t+1}(s) - V_t(s))`
  have hℓ : ∀ t s, ℓ t s ≤ η / (1 - γ) * (V (t + 1) s - V t s) := by
    intro t s
    have := npg_improvement hM hγ0 hγ1 hη t s
    have e : η / (1 - γ) * ((1 - γ) / η) = 1 := by field_simp
    calc ℓ t s = η / (1 - γ) * ((1 - γ) / η * ℓ t s) := by rw [← mul_assoc, e, one_mul]
      _ ≤ η / (1 - γ) * (V (t + 1) s - V t s) :=
          mul_le_mul_of_nonneg_left this (div_pos hη h1γ).le
  -- sum the steps
  have hsum : ∑ t ∈ range T, (Vstar s₀ - V t s₀) ≤
      1 / η * (∑ s, d s * Φ 0 s - ∑ s, d s * Φ T s) +
        (1 - γ)⁻¹ * (∑ s, d s * V T s - ∑ s, d s * V 0 s) := by
    have hle : ∀ t, Vstar s₀ - V t s₀ ≤ 1 / η * (∑ s, d s * Φ t s - ∑ s, d s * Φ (t + 1) s) +
        (1 - γ)⁻¹ * (∑ s, d s * V (t + 1) s - ∑ s, d s * V t s) := by
      intro t
      rw [hstep t]
      have h2 : 1 / η * ∑ s, d s * ℓ t s ≤
          (1 - γ)⁻¹ * (∑ s, d s * V (t + 1) s - ∑ s, d s * V t s) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        have := mul_le_mul_of_nonneg_left (hℓ t s) (hd0 s)
        have e : 1 / η * (d s * (η / (1 - γ) * (V (t + 1) s - V t s))) =
            (1 - γ)⁻¹ * (d s * V (t + 1) s - d s * V t s) := by field_simp
        calc 1 / η * (d s * ℓ t s) ≤ 1 / η * (d s * (η / (1 - γ) * (V (t + 1) s - V t s))) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = _ := e
      have e : 1 / η * ∑ s, d s * (Φ t s - Φ (t + 1) s + ℓ t s) =
          1 / η * (∑ s, d s * Φ t s - ∑ s, d s * Φ (t + 1) s) + 1 / η * ∑ s, d s * ℓ t s := by
        rw [← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun s _ => by ring
      linarith
    calc ∑ t ∈ range T, (Vstar s₀ - V t s₀)
        ≤ ∑ t ∈ range T, (1 / η * (∑ s, d s * Φ t s - ∑ s, d s * Φ (t + 1) s) +
            (1 - γ)⁻¹ * (∑ s, d s * V (t + 1) s - ∑ s, d s * V t s)) :=
          Finset.sum_le_sum fun t _ => hle t
      _ = 1 / η * (∑ s, d s * Φ 0 s - ∑ s, d s * Φ T s) +
            (1 - γ)⁻¹ * (∑ s, d s * V T s - ∑ s, d s * V 0 s) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          have h1 := Finset.sum_range_sub (fun t => ∑ s, d s * V t s) T
          have h2 := Finset.sum_range_sub (fun t => ∑ s, d s * Φ t s) T
          rw [h1]
          have h3 : ∑ t ∈ range T, (∑ s, d s * Φ t s - ∑ s, d s * Φ (t + 1) s) =
              -(∑ s, d s * Φ T s - ∑ s, d s * Φ 0 s) := by
            rw [← h2, ← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun t _ => by ring
          rw [h3]
          ring
  -- the potential terms
  have hΦ0 : ∑ s, d s * Φ 0 s = log (Fintype.card A) := by
    have : ∀ s, Φ 0 s = log (Fintype.card A) := by
      intro s
      simp only [Φ, npgPolicy, npgLogits, softmax_zero_prob, one_div, log_inv, mul_neg,
        Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul, πs.sum_prob, one_mul]
    simp_rw [this, ← Finset.sum_mul, hd1, one_mul]
  have hΦT : 0 ≤ ∑ s, d s * Φ T s := by
    refine Finset.sum_nonneg fun s _ => mul_nonneg (hd0 s) ?_
    simp only [Φ, neg_nonneg]
    exact Finset.sum_nonpos fun a _ => mul_nonpos_of_nonneg_of_nonpos (πs.prob_nonneg s a)
      (log_nonpos (softmax_prob_pos _ s a).le (softmax_prob_le_one _ s a))
  have hVT : ∑ s, d s * V T s ≤ 1 / (1 - γ) := by
    calc ∑ s, d s * V T s ≤ ∑ s, d s * (1 / (1 - γ)) := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (stochValue_mem_Icc hM hγ0 hγ1 hr _ s).2 (hd0 s)
      _ = 1 / (1 - γ) := by rw [← Finset.sum_mul, hd1, one_mul]
  have hV0 : 0 ≤ ∑ s, d s * V 0 s := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hd0 s) (stochValue_mem_Icc hM hγ0 hγ1 hr _ s).1
  -- monotonicity: `T (V* - V_T) ≤ ∑_{t<T} (V* - V_t)`
  have hmono : (T : ℝ) * (Vstar s₀ - V T s₀) ≤ ∑ t ∈ range T, (Vstar s₀ - V t s₀) := by
    have := Finset.sum_le_sum fun t (ht : t ∈ range T) =>
      sub_le_sub_left (stochValue_npgPolicy_mono hM hγ0 hγ1 hη s₀
        (Finset.mem_range.1 ht).le : V t s₀ ≤ V T s₀) (Vstar s₀)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  have hTpos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have htotal : (T : ℝ) * (Vstar s₀ - V T s₀) ≤ log (Fintype.card A) / η + 1 / (1 - γ) ^ 2 := by
    have h1 : 1 / η * (∑ s, d s * Φ 0 s - ∑ s, d s * Φ T s) ≤ log (Fintype.card A) / η := by
      rw [hΦ0]
      calc 1 / η * (log (Fintype.card A) - ∑ s, d s * Φ T s) ≤ 1 / η * log (Fintype.card A) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = log (Fintype.card A) / η := by ring
    have h2 : (1 - γ)⁻¹ * (∑ s, d s * V T s - ∑ s, d s * V 0 s) ≤ 1 / (1 - γ) ^ 2 := by
      calc (1 - γ)⁻¹ * (∑ s, d s * V T s - ∑ s, d s * V 0 s) ≤ (1 - γ)⁻¹ * (1 / (1 - γ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 h1γ.le)
        _ = 1 / (1 - γ) ^ 2 := by field_simp
    linarith
  have : Vstar s₀ - V T s₀ ≤ (log (Fintype.card A) / η + 1 / (1 - γ) ^ 2) / T := by
    rw [le_div_iff₀ hTpos, mul_comm]
    exact htotal
  calc Vstar s₀ - V T s₀ ≤ (log (Fintype.card A) / η + 1 / (1 - γ) ^ 2) / T := this
    _ = log (Fintype.card A) / (η * T) + 1 / ((1 - γ) ^ 2 * T) := by
        field_simp

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
