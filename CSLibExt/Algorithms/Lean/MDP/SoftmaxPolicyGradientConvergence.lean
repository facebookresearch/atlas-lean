/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.SoftmaxPolicyGradient

/-!
# Global convergence of softmax policy gradient

The proof uses the limiting-advantage argument of Agarwal, Kakade, Lee and Mahajan,
*On the Theory of Policy Gradient Methods: Optimality, Approximation, and Distribution Shift*,
arXiv:1908.00261v5, Theorem 5.1 and Appendix C.1 (JMLR 22(98), Theorem 10).
The first step, policy improvement and vanishing updates, uses a direct exponential
inequality for the closed-form update instead of smoothness of the value objective.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Filter Real StochasticPolicy
open scoped Topology

-- This bound controls negative updates as well as positive ones.
private theorem mul_exp_sub_one_ge {K x : ℝ} (hK : 0 ≤ K) (hx : -K ≤ x) :
    exp (-K) * x ^ 2 ≤ x * (exp x - 1) := by
  by_cases hx0 : 0 ≤ x
  · have h₁ : exp (-K) ≤ 1 := by simpa using exp_le_exp.mpr (neg_nonpos.mpr hK)
    have h₂ : x ≤ exp x - 1 := by linarith [add_one_le_exp x]
    calc exp (-K) * x ^ 2 ≤ 1 * x ^ 2 := mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)
      _ = x * x := by ring
      _ ≤ x * (exp x - 1) := mul_le_mul_of_nonneg_left h₂ hx0
  · have h₁ := mul_le_mul_of_nonneg_left (add_one_le_exp (-x)) (exp_pos x).le
    rw [← exp_add, add_neg_cancel, exp_zero] at h₁
    have h₂ : exp x - 1 ≤ x * exp x := by linarith
    have h₃ : x * exp x ≤ x * exp (-K) :=
      mul_le_mul_of_nonpos_left (exp_le_exp.mpr hx) (le_of_not_ge hx0)
    calc exp (-K) * x ^ 2 = x * (x * exp (-K)) := by ring
      _ ≤ x * (exp x - 1) :=
        mul_le_mul_of_nonpos_left (h₂.trans h₃) (le_of_not_ge hx0)

private theorem exp_weighted_advantage_ge {c K w : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hw : -K ≤ c * w) : c * exp (-K) * w ^ 2 ≤ w * (exp (c * w) - 1) := by
  apply (mul_le_mul_iff_left₀ hc).mp
  calc c * exp (-K) * w ^ 2 * c = exp (-K) * (c * w) ^ 2 := by ring
    _ ≤ (c * w) * (exp (c * w) - 1) := mul_exp_sub_one_ge hK hw
    _ = w * (exp (c * w) - 1) * c := by ring

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
  {M : MDP S A ℝ} {γ : ℝ}

omit [Fintype S] [DecidableEq S] in
private theorem softmax_prob_add (θ d : S → A → ℝ) (s : S) (a : A) :
    (softmax (θ + d)).prob s a = (softmax θ).prob s a * exp (d s a) /
      (∑ b, (softmax θ).prob s b * exp (d s b)) := by
  simp only [softmax_prob, Pi.add_apply, exp_add, div_mul_eq_mul_div, ← sum_div]
  rw [div_div_div_cancel_right₀ (sum_exp_pos θ s).ne']

omit [Nonempty A] in
private theorem lower_bound_of_advantage (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (p q : StochasticPolicy S A)
    (h : ∀ s, 0 ≤ ∑ a, q.prob s a * advantage hM hγ0 hγ1 p s a) (s : S) :
    (∑ a, q.prob s a * advantage hM hγ0 hγ1 p s a) ≤
      stochValue M γ hM hγ0 hγ1 q s - stochValue M γ hM hγ0 hγ1 p s := by
  let g z := ∑ a, q.prob z a * advantage hM hγ0 hγ1 p z a
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  rw [performance_difference]
  change g s ≤ (1 - γ)⁻¹ * ∑ z, occupancy hM hγ0 hγ1 q s z * g z
  rw [← div_eq_inv_mul, le_div_iff₀ hγ, mul_comm (g s)]
  calc (1 - γ) * g s ≤ occupancy hM hγ0 hγ1 q s s * g s :=
        mul_le_mul_of_nonneg_right
          (one_sub_le_visitation_self (policyKernel_mem hM q) hγ0 hγ1 s) (h s)
    _ ≤ ∑ z, occupancy hM hγ0 hγ1 q s z * g z :=
      single_le_sum (fun z _ => mul_nonneg (occupancy_nonneg hM hγ0 hγ1 q s z) (h z))
        (mem_univ s)

private theorem softmax_value_gain (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (θ : S → A → ℝ) {c : S → ℝ} (hc : ∀ s, 0 < c s) {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ s a, |c s * ((softmax θ).prob s a *
      advantage hM hγ0 hγ1 (softmax θ) s a)| ≤ K) (s : S) (a : A) :
    let p := softmax θ
    let w s a := p.prob s a * advantage hM hγ0 hγ1 p s a
    let q := softmax (θ + fun s a => c s * w s a)
    c s * exp (-2 * K) * (w s a) ^ 2 ≤
      stochValue M γ hM hγ0 hγ1 q s - stochValue M γ hM hγ0 hγ1 p s := by
  dsimp only
  let p := softmax θ
  let w s a := p.prob s a * advantage hM hγ0 hγ1 p s a
  let d s a := c s * w s a
  let q := softmax (θ + d)
  let Z s := ∑ b, p.prob s b * exp (d s b)
  have hZ (s : S) : 0 < Z s := sum_pos
    (fun b _ => mul_pos (softmax_prob_pos θ s b) (exp_pos _)) univ_nonempty
  have hZle (s : S) : Z s ≤ exp K := by
    calc Z s ≤ ∑ b, p.prob s b * exp K := sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (exp_le_exp.mpr (abs_le.mp (hstep s b)).2)
            (p.prob_nonneg s b)
      _ = exp K := by rw [← sum_mul, p.sum_prob, one_mul]
  have hsum (s : S) : ∑ b, q.prob s b * advantage hM hγ0 hγ1 p s b =
      (∑ b, w s b * (exp (d s b) - 1)) / Z s := by
    change ∑ b, (softmax (θ + d)).prob s b * advantage hM hγ0 hγ1 p s b = _
    simp only [softmax_prob_add]
    change ∑ b, (p.prob s b * exp (d s b) / Z s) * advantage hM hγ0 hγ1 p s b = _
    simp_rw [div_mul_eq_mul_div, mul_right_comm (_ : ℝ) (exp _)]
    rw [← sum_div]
    congr 1
    simp_rw [mul_sub, mul_one, sum_sub_distrib]
    rw [show ∑ b, w s b = 0 from sum_prob_mul_advantage hM hγ0 hγ1 p s, sub_zero]
  have hterm (s : S) (b : A) : c s * exp (-K) * (w s b) ^ 2 ≤
      w s b * (exp (d s b) - 1) :=
    exp_weighted_advantage_ge (hc s) hK (abs_le.mp (hstep s b)).1
  have hnonneg (s : S) (b : A) : 0 ≤ w s b * (exp (d s b) - 1) :=
    (mul_nonneg (mul_nonneg (hc s).le (exp_pos _).le) (sq_nonneg _)).trans (hterm s b)
  change _ ≤ stochValue M γ hM hγ0 hγ1 q s - stochValue M γ hM hγ0 hγ1 p s
  refine le_trans ?_ (lower_bound_of_advantage hM hγ0 hγ1 p q (fun z => by
    rw [hsum]; exact div_nonneg (sum_nonneg fun b _ => hnonneg z b) (hZ z).le) s)
  rw [hsum, le_div_iff₀ (hZ s)]
  calc c s * exp (-2 * K) * (w s a) ^ 2 * Z s ≤
      c s * exp (-2 * K) * (w s a) ^ 2 * exp K :=
        mul_le_mul_of_nonneg_left (hZle s)
          (mul_nonneg (mul_nonneg (hc s).le (exp_pos _).le) (sq_nonneg _))
    _ = c s * exp (-K) * (w s a) ^ 2 := by
      rw [mul_right_comm _ ((w s a) ^ 2), mul_assoc (c s), ← exp_add]
      congr 3
      ring
    _ ≤ w s a * (exp (d s a) - 1) := hterm s a
    _ ≤ ∑ b, w s b * (exp (d s b) - 1) :=
      single_le_sum (fun b _ => hnonneg s b) (mem_univ a)

section OneState

variable {ι : Type*} [Fintype ι]

private theorem tends_zero_of_mul_tends_zero {p g : ℕ → ℝ} {b : ℝ}
    (hg : Tendsto g atTop (𝓝 b)) (hb : b ≠ 0)
    (hpg : Tendsto (fun t => p t * g t) atTop (𝓝 0)) :
    Tendsto p atTop (𝓝 0) := by
  have h := hpg.div hg hb
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [hg.eventually_ne hb] with t ht
  exact mul_div_cancel_right₀ _ ht

omit [Fintype ι] in
private theorem le_of_sum_le_of_lower_bounds [DecidableEq ι] {B : Finset ι} {a : ι}
    (ha : a ∈ B) {x : ι → ℝ} {L U : ℝ} (hL : ∀ b ∈ B, L ≤ x b)
    (hU : ∑ b ∈ B, x b ≤ U) :
    x a ≤ U - (B.erase a).card * L := by
  have h := sum_le_sum (s := B.erase a) fun b hb => hL b (mem_of_mem_erase hb)
  rw [sum_const, nsmul_eq_mul] at h
  have he := sum_erase_add B x ha
  linarith

private theorem prob_relation {θ : ℕ → ι → ℝ} {p : ℕ → ι → ℝ}
    (hp : ∀ t a, p t a = exp (θ t a) / ∑ b, exp (θ t b)) (t : ℕ) (a b : ι) :
    p t a = exp (θ t a - θ t b) * p t b := by
  rw [hp t a, hp t b, ← mul_div_assoc, ← exp_add, sub_add_cancel]

-- The comparison below is a tail-bound version of the last-excursion argument in
-- AKLM Lemma C.11. If an eventually negative logit stayed above L, then any logit
-- below L could lose at most a constant times the loss of that negative logit.
private theorem not_bddBelow_of_negative_limit [Nonempty ι]
    {θ p g : ℕ → ι → ℝ} {c : ℕ → ℝ} {K B : ℝ} (hB : 0 < B)
    (hp : ∀ t a, p t a = exp (θ t a) / ∑ b, exp (θ t b))
    (hc : ∀ t, 0 ≤ c t) (hg : ∀ t a, |g t a| ≤ B)
    (hstep : ∀ t a, θ (t + 1) a = θ t a + c t * (p t a * g t a))
    (hstepBound : ∀ t a, |c t * (p t a * g t a)| ≤ K)
    (hsum : ∀ t, ∑ a, θ t a = ∑ a, θ 0 a)
    {aPlus aMinus : ι} (hzero : Tendsto (fun t => p t aPlus) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hpos : ∀ t ≥ N, 0 ≤ g t aPlus) (hneg : ∀ t ≥ N, g t aMinus ≤ -δ) :
    ¬ ∃ L : ℝ, ∀ t ≥ N, L ≤ θ t aMinus := by
  classical
  rintro ⟨L, hL⟩
  have hp0 (t : ℕ) (a : ι) : 0 ≤ p t a := by
    rw [hp]
    exact div_nonneg (exp_pos _).le (sum_nonneg fun b _ => (exp_pos (θ t b)).le)
  have hplus (t : ℕ) (ht : N ≤ t) : θ N aPlus ≤ θ t aPlus := by
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      rw [hstep]
      exact ih.trans (le_add_of_nonneg_right (mul_nonneg (hc t)
        (mul_nonneg (hp0 t aPlus) (hpos t ht))))
  let C := B / δ
  have hC : 0 < C := div_pos hB hδ
  have hdec (t : ℕ) (ht : N ≤ t) : θ (t + 1) aMinus ≤ θ t aMinus := by
    rw [hstep]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (hc t)
      (mul_nonpos_of_nonneg_of_nonpos (hp0 t aMinus) (by linarith [hneg t ht])))
  have hmono (t : ℕ) (ht : N ≤ t) : θ t aMinus ≤ θ N aMinus := by
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih => exact (hdec t ht).trans ih
  let l := min (L - K) (univ.inf' univ_nonempty (θ N))
  have hlow (b : ι) (t : ℕ) (ht : N ≤ t) :
      l - C * (θ N aMinus - θ t aMinus) ≤ θ t b := by
    induction t, ht using Nat.le_induction with
    | base =>
      simpa only [sub_self, mul_zero, sub_zero] using
        (min_le_right _ _).trans (inf'_le _ (mem_univ b))
    | succ t ht ih =>
      by_cases hb : L ≤ θ t b
      · have h := (abs_le.mp (hstepBound t b)).1
        have he := hstep t b
        have hC' := mul_nonneg hC.le (sub_nonneg.mpr (hmono (t + 1) (by omega)))
        have hl : l ≤ L - K := min_le_left _ _
        linarith
      · have hpb : p t b ≤ p t aMinus := by
          rw [hp t b, hp t aMinus]
          exact div_le_div_of_nonneg_right
            (exp_le_exp.mpr ((le_of_not_ge hb).trans (hL t ht)))
            (sum_nonneg fun a _ => (exp_pos (θ t a)).le)
        have hdelta : C * δ = B := div_mul_cancel₀ _ hδ.ne'
        have hcmp : C * (p t aMinus * g t aMinus) ≤ p t b * g t b := calc
          _ ≤ C * (p t aMinus * -δ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hneg t ht)
              (hp0 t aMinus)) hC.le
          _ = p t aMinus * -B := by linear_combination -(p t aMinus) * hdelta
          _ ≤ p t b * -B := mul_le_mul_of_nonpos_right hpb (neg_nonpos.mpr hB.le)
          _ ≤ _ := mul_le_mul_of_nonneg_left (abs_le.mp (hg t b)).1 (hp0 t b)
        have hstepCmp := mul_le_mul_of_nonneg_left hcmp (hc t)
        rw [hstep t b, hstep t aMinus]
        linarith only [ih, hstepCmp]
  let L' := l - C * (θ N aMinus - L)
  have hL' (b : ι) (t : ℕ) (ht : N ≤ t) : L' ≤ θ t b := by
    refine le_trans ?_ (hlow b t ht)
    dsimp [L']
    gcongr
    exact hL t ht
  let U := (∑ a, θ 0 a) - (Fintype.card ι - 1 : ℕ) * L'
  have hU (b : ι) (t : ℕ) (ht : N ≤ t) : θ t b ≤ U := by
    have h := le_of_sum_le_of_lower_bounds (mem_univ b) (x := θ t)
      (fun a _ => hL' a t ht) (hsum t).le
    simpa only [U, card_erase_of_mem (mem_univ b), card_univ] using h
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < (Fintype.card ι : ℝ) * exp U := mul_pos hcard (exp_pos _)
  have hbound : ∀ᶠ t in atTop, exp (θ N aPlus) / ((Fintype.card ι : ℝ) * exp U) ≤ p t aPlus := by
    filter_upwards [eventually_ge_atTop N] with t ht
    have hsumexp : (∑ a, exp (θ t a)) ≤ (Fintype.card ι : ℝ) * exp U := by
      simpa only [sum_const, nsmul_eq_mul, card_univ] using
        (sum_le_sum (s := (univ : Finset ι)) fun a _ => exp_le_exp.mpr (hU a t ht))
    rw [hp t aPlus]
    exact div_le_div₀ (exp_pos _).le (exp_le_exp.mpr (hplus t ht))
      (sum_pos (fun a _ => exp_pos (θ t a)) univ_nonempty) hsumexp
  exact (not_le_of_gt (div_pos (exp_pos _) hden)) (ge_of_tendsto hzero hbound)

-- The positive and negative limiting-advantage actions lose all probability. For
-- the zero-limit actions, retain only those whose logit never drops below the
-- positive reference action. Their sum would have to be both bounded and unbounded.
private theorem limit_advantage_nonpos [Nonempty ι]
    {θ p g : ℕ → ι → ℝ} {c : ℕ → ℝ} {gLim : ι → ℝ} {K B : ℝ} (hB : 0 < B)
    (hp : ∀ t a, p t a = exp (θ t a) / ∑ b, exp (θ t b))
    (hp1 : ∀ t, ∑ a, p t a = 1) (hc : ∀ t, 0 ≤ c t)
    (hg : ∀ t a, |g t a| ≤ B)
    (hstep : ∀ t a, θ (t + 1) a = θ t a + c t * (p t a * g t a))
    (hstepBound : ∀ t a, |c t * (p t a * g t a)| ≤ K)
    (hmean : ∀ t, ∑ a, p t a * g t a = 0)
    (hlim : ∀ a, Tendsto (fun t => g t a) atTop (𝓝 (gLim a)))
    (hvanish : ∀ a, Tendsto (fun t => p t a * g t a) atTop (𝓝 0)) (aPlus : ι) :
    gLim aPlus ≤ 0 := by
  classical
  by_contra! hPositive
  have hpp (t : ℕ) (a : ι) : 0 < p t a := by
    rw [hp]
    exact div_pos (exp_pos _) (sum_pos (fun a _ => exp_pos (θ t a)) univ_nonempty)
  have hrank (t : ℕ) {a b : ι} (h : θ t a ≤ θ t b) : p t a ≤ p t b := by
    rw [prob_relation hp t a b]
    have hExp : exp (θ t a - θ t b) ≤ 1 := by
      simpa only [exp_zero] using exp_le_exp.mpr (sub_nonpos.mpr h)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hExp (hpp t b).le
  have hsum (t : ℕ) : ∑ a, θ t a = ∑ a, θ 0 a := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp_rw [hstep, sum_add_distrib, ← mul_sum, hmean, mul_zero, add_zero, ih]
  have hpZero (a : ι) (ha : gLim a ≠ 0) : Tendsto (fun t => p t a) atTop (𝓝 0) :=
    tends_zero_of_mul_tends_zero (hlim a) ha (hvanish a)
  have hpPlus := hpZero aPlus hPositive.ne'
  let δ := gLim aPlus / 2
  have hδ : 0 < δ := half_pos hPositive
  have hpos : ∀ᶠ t in atTop, δ ≤ g t aPlus :=
    (tendsto_const_nhds.eventually_lt (hlim aPlus) (half_lt_self hPositive)).mono
      (fun _ h => h.le)
  have hsep : ∀ᶠ t in atTop, ∀ a, gLim a = 0 → g t a ≤ g t aPlus := by
    apply eventually_all.mpr
    intro a
    by_cases ha : gLim a = 0
    · exact ((hlim a).eventually_lt (hlim aPlus) (ha ▸ hPositive)).mono
        (fun _ ht _ => ht.le)
    · exact Eventually.of_forall (fun _ h => False.elim (ha h))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpos.and hsep)
  let L := θ N aPlus
  have hL (t : ℕ) (ht : N ≤ t) : L ≤ θ t aPlus := by
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      rw [hstep]
      exact ih.trans (le_add_of_nonneg_right (mul_nonneg (hc t)
        (mul_nonneg (hpp t aPlus).le (hδ.le.trans (hN t ht).1))))
  -- Negative limiting advantage forces the logit to −∞ (C.11).
  have hnegLogit (a : ι) (ha : gLim a < 0) : Tendsto (fun t => θ t a) atTop atBot := by
    let δ' := -gLim a / 2
    have hδ' : 0 < δ' := half_pos (neg_pos.mpr ha)
    have hn : ∀ᶠ t in atTop, g t a ≤ -δ' :=
      ((hlim a).eventually_lt tendsto_const_nhds (by dsimp [δ']; linarith)).mono
        (fun _ ht => ht.le)
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hn.and (eventually_ge_atTop N))
    have hno := not_bddBelow_of_negative_limit hB hp hc hg hstep hstepBound hsum hpPlus hδ'
      (N := J) (fun t ht => hδ.le.trans (hN t (hJ t ht).2).1) (fun t ht => (hJ t ht).1)
    apply tendsto_atBot.mpr
    intro b
    push Not at hno
    obtain ⟨j, hj, hjb⟩ := hno b
    apply eventually_atTop.mpr
    refine ⟨j, fun t ht => hjb.le.trans' ?_⟩
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      rw [hstep]
      exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (hc t)
        (mul_nonpos_of_nonneg_of_nonpos (hpp t a).le
          ((hJ t (hj.trans ht)).1.trans (neg_nonpos.mpr hδ'.le))))).trans ih
  -- `D` is the source's set B₀: zero-limit actions that stay ahead of `aPlus`.
  let D := univ.filter fun a => gLim a = 0 ∧ ∀ t ≥ N, θ t aPlus < θ t a
  have hD (a : ι) (ha : a ∈ D) : ∀ t ≥ N, L ≤ θ t a := fun t ht =>
    (hL t ht).trans ((mem_filter.mp ha).2.2 t ht).le
  have hstay (a : ι) (ha : a ∉ D) (ha0 : gLim a = 0) :
      ∀ᶠ t in atTop, θ t a ≤ θ t aPlus := by
    have hex : ¬ ∀ t ≥ N, θ t aPlus < θ t a := fun h => ha (mem_filter.mpr
      ⟨mem_univ _, ha0, h⟩)
    push Not at hex
    obtain ⟨j, hj, hja⟩ := hex
    apply eventually_atTop.mpr
    refine ⟨j, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base => exact hja
    | succ t ht ih =>
      have ht' := hN t (hj.trans ht)
      have hinc : p t a * g t a ≤ p t aPlus * g t aPlus :=
        (mul_le_mul_of_nonneg_left (ht'.2 a ha0) (hpp t a).le).trans
          (mul_le_mul_of_nonneg_right (hrank t ih) (hδ.le.trans ht'.1))
      rw [hstep t a, hstep t aPlus]
      exact add_le_add ih (mul_le_mul_of_nonneg_left hinc (hc t))
  have hDout (a : ι) (ha : a ∉ D) : Tendsto (fun t => p t a) atTop (𝓝 0) := by
    by_cases ha0 : gLim a = 0
    · exact squeeze_zero' (Eventually.of_forall (fun t => (hpp t a).le))
        ((hstay a ha ha0).mono (fun t ht => hrank t ht)) hpPlus
    · exact hpZero a ha0
  let ε := δ / (Fintype.card ι + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  -- The complement of D contributes at least the positive reference term minus
  -- one ε-sized error (relative to its probability) for each remaining action.
  have hsmall (a : ι) (ha : a ∉ D) :
      ∀ᶠ t in atTop, -(p t aPlus * ε) ≤ p t a * g t a := by
    rcases lt_trichotomy (gLim a) 0 with hneg | hzero | hgt
    · have hbot : Tendsto (fun t => θ t a - θ t aPlus) atTop atBot := by
        apply tendsto_atBot.mpr
        intro x
        filter_upwards [tendsto_atBot.mp (hnegLogit a hneg) (x + L),
          eventually_ge_atTop N] with t ht hN'
        linarith [hL t hN']
      have he : Tendsto (fun t => exp (θ t a - θ t aPlus) * B) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, zero_mul] using
          (tendsto_exp_atBot.comp hbot).mul_const B
      filter_upwards [he.eventually_lt tendsto_const_nhds hε] with t ht
      rw [prob_relation hp t a aPlus]
      calc -(p t aPlus * ε) ≤ -(p t aPlus * (exp (θ t a - θ t aPlus) * B)) :=
            neg_le_neg (mul_le_mul_of_nonneg_left ht.le (hpp t aPlus).le)
        _ = p t aPlus * (exp (θ t a - θ t aPlus) * -B) := by ring
        _ ≤ p t aPlus * (exp (θ t a - θ t aPlus) * g t a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_le.mp (hg t a)).1
            (exp_pos _).le) (hpp t aPlus).le
        _ = _ := by ring
    · obtain ⟨j, hj⟩ := Metric.tendsto_atTop.mp (hzero ▸ hlim a) ε hε
      filter_upwards [hstay a ha hzero, eventually_ge_atTop j] with t ht hjt
      have hg' : -ε ≤ g t a := by
        have h := hj t hjt
        rw [Real.dist_eq, sub_zero] at h
        exact (abs_lt.mp h).1.le
      calc -(p t aPlus * ε) = p t aPlus * -ε := by ring
        _ ≤ p t a * -ε := mul_le_mul_of_nonpos_right (hrank t ht) (neg_nonpos.mpr hε.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left hg' (hpp t a).le
    · filter_upwards [tendsto_const_nhds.eventually_lt (hlim a) hgt] with t ht
      exact (neg_nonpos.mpr (mul_nonneg (hpp t aPlus).le hε.le)).trans
        (mul_nonneg (hpp t a).le ht.le)
  have hplusD : aPlus ∉ D := fun h => hPositive.ne' (mem_filter.mp h).2.1
  let E := univ.filter (· ∉ D)
  have hplusE : aPlus ∈ E := mem_filter.mpr ⟨mem_univ _, hplusD⟩
  have hE (t : ℕ) : (∑ a ∈ D, p t a * g t a) + (∑ a ∈ E, p t a * g t a) = 0 := by
    have h := sum_filter_add_sum_filter_not (univ : Finset ι) (· ∈ D)
      (fun a => p t a * g t a)
    have h' : univ.filter (· ∈ D) = D := by ext a; simp
    rw [h', hmean] at h
    exact h
  have hinc : ∀ᶠ t in atTop, 0 ≤ ∑ a ∈ E, p t a * g t a := by
    have hsmall' : ∀ᶠ t in atTop, ∀ a ∈ E.erase aPlus, -(p t aPlus * ε) ≤ p t a * g t a :=
      (eventually_all_finset _).mpr fun a ha => hsmall a (mem_filter.mp
        (mem_of_mem_erase ha)).2
    filter_upwards [hsmall', hpos] with t ht htp
    have h := sum_le_sum ht
    rw [sum_const, nsmul_eq_mul] at h
    have hcard : ((E.erase aPlus).card : ℝ) ≤ Fintype.card ι :=
      Nat.cast_le.mpr (card_le_univ _)
    have hbudget : ((E.erase aPlus).card : ℝ) * ε ≤ δ := by
      dsimp [ε]
      rw [← mul_div_assoc, div_le_iff₀ (show (0 : ℝ) < Fintype.card ι + 1 by positivity)]
      simpa only [mul_comm (δ : ℝ) (Fintype.card ι + 1)] using
        mul_le_mul_of_nonneg_right (hcard.trans (le_add_of_nonneg_right zero_le_one)) hδ.le
    have href := mul_le_mul_of_nonneg_left htp (hpp t aPlus).le
    have hcost := mul_le_mul_of_nonneg_left hbudget (hpp t aPlus).le
    have he := sum_erase_add E (fun a => p t a * g t a) hplusE
    nlinarith only [h, href, hcost, he]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hinc.and (eventually_ge_atTop N))
  have hDsum (t : ℕ) (ht : J ≤ t) : ∑ a ∈ D, θ t a ≤ ∑ a ∈ D, θ J a := by
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      have hnonpos : ∑ a ∈ D, p t a * g t a ≤ 0 := by linarith [hE t, (hJ t ht).1]
      simp_rw [hstep, sum_add_distrib, ← mul_sum]
      exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (hc t) hnonpos)).trans ih
  -- A bounded sum and a common lower bound would bound every logit in D.
  -- Then their probabilities would also vanish, contradicting total mass 1.
  have hall (a : ι) : Tendsto (fun t => p t a) atTop (𝓝 0) := by
    by_cases ha : a ∈ D
    · let U := (∑ b ∈ D, θ J b) - (D.erase a).card * L
      have hb : ∀ᶠ t in atTop, p t a ≤ exp (U - L) * p t aPlus := by
        filter_upwards [eventually_ge_atTop J] with t ht
        have hN' := (hJ t ht).2
        have hu : θ t a ≤ U := le_of_sum_le_of_lower_bounds ha
          (fun b hb => hD b hb t hN') (hDsum t ht)
        rw [prob_relation hp t a aPlus]
        exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (sub_le_sub hu (hL t hN')))
          (hpp t aPlus).le
      exact squeeze_zero' (Eventually.of_forall (fun t => (hpp t a).le)) hb
        (by simpa only [mul_zero] using hpPlus.const_mul (exp (U - L)))
    · exact hDout a ha
  have h := tendsto_finsetSum (univ : Finset ι) (fun a _ => hall a)
  simp only [sum_const_zero, hp1] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

end OneState

omit [Nonempty A] in
private theorem abs_advantage_le (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) (p : StochasticPolicy S A)
    (s : S) (a : A) : |advantage hM hγ0 hγ1 p s a| ≤ (1 - γ)⁻¹ := by
  let B := (1 - γ)⁻¹
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hv (z : S) : stochValue M γ hM hγ0 hγ1 p z ∈ Set.Icc 0 B := by
    simpa only [B, one_div] using stochValue_mem_Icc hM hγ0 hγ1 hr p z
  have hq0 : 0 ≤ stochQValue hM hγ0 hγ1 p s a := by
    exact add_nonneg (hr s a).1 (mul_nonneg hγ0 (sum_nonneg fun z _ =>
      mul_nonneg (hM.1 s a z) (hv z).1))
  have hq1 : stochQValue hM hγ0 hγ1 p s a ≤ B := calc
    _ ≤ 1 + γ * ∑ z, M.prob s a z * B := add_le_add (hr s a).2
      (mul_le_mul_of_nonneg_left (sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (hv z).2 (hM.1 s a z)) hγ0)
    _ = B := by
      rw [← sum_mul, hM.2, one_mul]
      dsimp [B]
      field_simp [hγ.ne']
      ring
  change |stochQValue hM hγ0 hγ1 p s a - stochValue M γ hM hγ0 hγ1 p s| ≤ B
  exact abs_le.mpr ⟨by linarith [hq0, (hv s).2], by linarith [hq1, (hv s).1]⟩

omit [Nonempty A] in
private theorem occupancy_initial_bounds (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (p : StochasticPolicy S A) {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1) (s : S) :
    (1 - γ) * μ s ≤ ∑ z, μ z * occupancy hM hγ0 hγ1 p z s ∧
      ∑ z, μ z * occupancy hM hγ0 hγ1 p z s ≤ 1 := by
  constructor
  · rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left
      (one_sub_le_visitation_self (policyKernel_mem hM p) hγ0 hγ1 s) (hμ s)).trans
      (single_le_sum (fun z _ => mul_nonneg (hμ z) (occupancy_nonneg hM hγ0 hγ1 p z s))
        (mem_univ s))
  · calc ∑ z, μ z * occupancy hM hγ0 hγ1 p z s ≤ ∑ z, μ z := by
          refine sum_le_sum fun z _ => ?_
          have h := single_le_sum (fun w _ => occupancy_nonneg hM hγ0 hγ1 p z w) (mem_univ s)
          rw [sum_occupancy] at h
          exact mul_le_of_le_one_right (hμ z) h
      _ = 1 := hμ1

-- No differentiability theorem is needed once the update is written in closed form.
private theorem tendsto_stochValue_of_softmax_updates
    (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) {μ : S → ℝ}
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ (1 - γ) ^ 3 / 8) (θ : ℕ → S → A → ℝ)
    (hupdate : ∀ t s a, θ (t + 1) s a = θ t s a +
      η * (1 - γ)⁻¹ * (∑ z, μ z * occupancy hM hγ0 hγ1 (softmax (θ t)) z s) *
        ((softmax (θ t)).prob s a * advantage hM hγ0 hγ1 (softmax (θ t)) s a)) (s : S) :
    Tendsto (fun t => stochValue M γ hM hγ0 hγ1 (softmax (θ t)) s) atTop
      (𝓝 (optimalValue M γ hM hγ0 hγ1 s)) := by
  let p t := softmax (θ t)
  let V t := stochValue M γ hM hγ0 hγ1 (p t)
  let g t := advantage hM hγ0 hγ1 (p t)
  let c t (z : S) := η * (1 - γ)⁻¹ * ∑ w, μ w * occupancy hM hγ0 hγ1 (p t) w z
  let B := (1 - γ)⁻¹
  let K := (1 - γ) / 8
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ1
  have hB : 0 < B := inv_pos.mpr hγ
  have hK : 0 ≤ K := (div_pos hγ (by norm_num)).le
  have hηBB : η * B * B ≤ K := calc
    _ ≤ ((1 - γ) ^ 3 / 8) * B * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hη hB.le) hB.le
    _ = K := by
      dsimp [B, K]
      field_simp [hγ.ne']
  have hc (t : ℕ) (z : S) : η * μ z ≤ c t z ∧ c t z ≤ η * B := by
    have h := occupancy_initial_bounds hM hγ0 hγ1 (p t) (fun w => (hμ w).le) hμ1 z
    have hηB : 0 ≤ η * B := mul_nonneg hη0.le hB.le
    constructor
    · calc η * μ z = η * B * ((1 - γ) * μ z) := by dsimp [B]; field_simp [hγ.ne']
        _ ≤ c t z := mul_le_mul_of_nonneg_left h.1 hηB
    · exact mul_le_of_le_one_right hηB h.2
  have hcpos (t : ℕ) (z : S) : 0 < c t z := (mul_pos hη0 (hμ z)).trans_le (hc t z).1
  have hg (t : ℕ) (z : S) (a : A) : |g t z a| ≤ B := abs_advantage_le hM hγ0 hγ1 hr _ _ _
  have hstep (t : ℕ) (z : S) (a : A) : θ (t + 1) z a = θ t z a +
      c t z * ((p t).prob z a * g t z a) := hupdate t z a
  have hstepBound (t : ℕ) (z : S) (a : A) : |c t z * ((p t).prob z a * g t z a)| ≤ K := by
    rw [abs_mul, abs_of_pos (hcpos t z), abs_mul, abs_of_nonneg ((p t).prob_nonneg z a)]
    have hw : (p t).prob z a * |g t z a| ≤ B :=
      (mul_le_of_le_one_left (abs_nonneg _) (softmax_prob_le_one (θ t) z a)).trans (hg t z a)
    exact (mul_le_mul (hc t z).2 hw
      (mul_nonneg ((p t).prob_nonneg z a) (abs_nonneg _)) (mul_nonneg hη0.le hB.le)).trans hηBB
  have hgain (t : ℕ) (z : S) (a : A) :
      c t z * exp (-2 * K) * ((p t).prob z a * g t z a) ^ 2 ≤ V (t + 1) z - V t z := by
    have ht : θ (t + 1) = θ t + fun z a => c t z * ((p t).prob z a * g t z a) :=
      funext fun z => funext fun a => hstep t z a
    change _ ≤ stochValue M γ hM hγ0 hγ1 (softmax (θ (t + 1))) z - V t z
    rw [ht]
    exact softmax_value_gain hM hγ0 hγ1 (θ t) (hcpos t) hK (hstepBound t) z a
  have hmono (z : S) : Monotone (fun t => V t z) := by
    refine monotone_nat_of_le_succ fun t => sub_nonneg.mp ?_
    let a := Classical.choice (inferInstance : Nonempty A)
    exact (mul_nonneg (mul_nonneg (hcpos t z).le (exp_pos _).le) (sq_nonneg _)).trans
      (hgain t z a)
  have hbdd (z : S) : BddAbove (Set.range fun t => V t z) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨t, rfl⟩
    simpa only [B, one_div] using (stochValue_mem_Icc hM hγ0 hγ1 hr (p t) z).2
  let VLim z := ⨆ t, V t z
  have hV (z : S) : Tendsto (fun t => V t z) atTop (𝓝 (VLim z)) :=
    tendsto_atTop_ciSup (hmono z) (hbdd z)
  have hVanishing (z : S) (a : A) :
      Tendsto (fun t => (p t).prob z a * g t z a) atTop (𝓝 0) := by
    let k := η * μ z * exp (-2 * K)
    have hk : 0 < k := mul_pos (mul_pos hη0 (hμ z)) (exp_pos _)
    have hdiff : Tendsto (fun t => V (t + 1) z - V t z) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self] using
        ((hV z).comp (tendsto_add_atTop_nat 1)).sub (hV z)
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiff (k * ε ^ 2) (mul_pos hk (sq_pos_of_pos hε))
    refine ⟨N, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero]
    by_contra! h
    have h₁ : k * ε ^ 2 ≤ k * ((p t).prob z a * g t z a) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hk.le
      simpa only [sq_abs] using pow_le_pow_left₀ hε.le h 2
    have h₂ : k * ((p t).prob z a * g t z a) ^ 2 ≤
        c t z * exp (-2 * K) * ((p t).prob z a * g t z a) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc t z).1 (exp_pos _).le)
        (sq_nonneg _)
    have h₃ := hN t ht
    rw [Real.dist_eq, sub_zero] at h₃
    exact ((h₁.trans (h₂.trans (hgain t z a))).trans (le_abs_self _)).not_gt h₃
  have hgLim (z : S) (a : A) :
      Tendsto (fun t => g t z a) atTop (𝓝 (qValue M γ VLim z a - VLim z)) := by
    have hq : Tendsto (fun t => qValue M γ (V t) z a) atTop (𝓝 (qValue M γ VLim z a)) := by
      have hs := tendsto_finsetSum (univ : Finset S)
        (fun w _ => (hV w).const_mul (M.prob z a w))
      exact tendsto_const_nhds.add (hs.const_mul γ)
    exact hq.sub (hV z)
  have hnonpos (z : S) (a : A) : qValue M γ VLim z a - VLim z ≤ 0 :=
    limit_advantage_nonpos hB (fun t b => softmax_prob (θ t) z b) (fun t => (p t).sum_prob z)
      (fun t => (hcpos t z).le) (fun t => hg t z) (fun t => hstep t z)
      (fun t => hstepBound t z) (fun t => sum_prob_mul_advantage hM hγ0 hγ1 (p t) z)
      (hgLim z) (hVanishing z) a
  have hfixed : bellman M γ VLim = VLim := by
    funext z
    apply le_antisymm
    · exact sup'_le _ _ (fun a _ => sub_nonpos.mp (hnonpos z a))
    · refine le_of_tendsto (hV z) (Eventually.of_forall fun t => ?_)
      have hle : V t ≤ VLim := fun w => le_ciSup (hbdd w) t
      change stochValue M γ hM hγ0 hγ1 (p t) z ≤ _
      rw [stochValue_eq hM hγ0 hγ1 (p t) z]
      calc ∑ a, (p t).prob z a * qValue M γ (V t) z a
          ≤ ∑ a, (p t).prob z a * bellman M γ VLim z := sum_le_sum fun a ha =>
            mul_le_mul_of_nonneg_left ((qValue_mono hM hγ0 hle z a).trans
              (le_sup' (qValue M γ VLim z) ha)) ((p t).prob_nonneg z a)
        _ = bellman M γ VLim z := by rw [← sum_mul, (p t).sum_prob, one_mul]
  rw [← eq_optimalValue_of_bellman_eq hM hγ0 hγ1 hfixed]
  exact hV s

@[expose] public section

/-- Gradient ascent on the softmax objective from `θ_0 = 0`, with step size `η`:
`θ_{t+1} = θ_t + η ∇_θ V^{π_{θ_t}}(μ)`, the gradient written in the closed form of
`hasDerivAt_softmaxObjective` (AKLM equation (11); AJKS Chapter 12, equation (0.2)). -/
noncomputable def softmaxPGLogits (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → ℝ)
    (η : ℝ) : ℕ → S → A → ℝ
  | 0 => 0
  | t + 1 => fun s a => softmaxPGLogits hM hγ0 hγ1 μ η t s a +
      η * softmaxPolicyGradient hM hγ0 hγ1 μ (softmaxPGLogits hM hγ0 hγ1 μ η t) s a

/-- **Global convergence of softmax policy gradient** (AKLM Theorem 5.1; AJKS Theorem 12.3): for
rewards in `[0, 1]`, a start distribution `μ` charging every state and a step size
`0 < η ≤ (1 - γ)³ / 8`, the values of the gradient-ascent iterates converge to the optimal
value in every state. The iterates start from `θ_0 = 0`, a special case: the source fixes no
initialization. -/
theorem tendsto_stochValue_softmaxPGLogits (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) (μ : S → ℝ)
    (hμ : ∀ s, 0 < μ s) (hμ1 : ∑ s, μ s = 1) {η : ℝ} (hη0 : 0 < η)
    (hη : η ≤ (1 - γ) ^ 3 / 8) (s : S) :
    Filter.Tendsto (fun t => stochValue M γ hM hγ0 hγ1
        (softmax (softmaxPGLogits hM hγ0 hγ1 μ η t)) s) Filter.atTop
      (nhds (optimalValue M γ hM hγ0 hγ1 s)) := by
  refine tendsto_stochValue_of_softmax_updates hM hγ0 hγ1 hr hμ hμ1 hη0 hη
    (softmaxPGLogits hM hγ0 hγ1 μ η) (fun t z a => ?_) s
  rw [softmaxPGLogits]
  unfold softmaxPolicyGradient
  ring

end

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
