/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The classical secretary problem: the optimal threshold and the `1/e` law

In the classical secretary problem (Ferguson, *Optimal Stopping and Applications*, Chapter 2,
§2.1) `n` applicants arrive in uniformly random order and one may only use their relative
ranks. An optimal rule is a threshold rule `N_r`: reject the first `r - 1` applicants and accept
the next one that is best so far. Its probability of selecting the best applicant is Ferguson's
equation (3),
`P_r = ((r - 1)/n) ∑_{k=r}^{n} 1/(k - 1)` for `r ≥ 2`, and `P_1 = 1/n`,
which we write uniformly as `P_r = (1 + (r - 1) T_r)/n` with `T_r = ∑_{j=r}^{n-1} 1/j`.

This file proves the analytic part of Ferguson's §2.1:

* `MathlibExt.Probability.Secretary.winProb_le_winProb_optimalThreshold`: the threshold
  `r₁ = min {r ≥ 1 : ∑_{k=r+1}^{n} 1/(k - 1) ≤ 1}` of Ferguson's equation (4) maximises `P_r`
  over `1 ≤ r ≤ n`;
* `MathlibExt.Probability.Secretary.tendsto_optimalThreshold_div` and
  `MathlibExt.Probability.Secretary.tendsto_winProb_optimalThreshold`: `r₁/n → 1/e` and
  `P_{r₁} → 1/e` as `n → ∞`.

Equation (3) itself is derived from the random-order model in
`MathlibExt.Probability.OptimalStopping.SecretaryModel`, and
`MathlibExt.Probability.Secretary.card_rankRule_wins_div_factorial_le` in
`MathlibExt.Probability.OptimalStopping.SecretaryOptimality` shows that no rule based on relative
ranks does better than `N_{r₁}`.
-/

@[expose] public section

open Filter Topology Finset

namespace MathlibExt.Probability.Secretary

/-- **Harmonic tail of the secretary problem.** `T n r = ∑_{j=r}^{n-1} 1/j`, which equals
`∑_{k=r+1}^{n} 1/(k - 1)` in Ferguson's notation (*Optimal Stopping and Applications*,
Chapter 2, equation (4)). -/
noncomputable def harmonicTail (n r : ℕ) : ℝ := ∑ j ∈ Ico r n, (1 : ℝ) / j

/-- **Win probability of a threshold rule in the secretary problem.** For `n` applicants and
threshold `1 ≤ r ≤ n`, `P_r = (1 + (r - 1) T_r)/n` with `T_r = ∑_{j=r}^{n-1} 1/j`; this is
Ferguson's equation (3), `P_r = ((r - 1)/n) ∑_{k=r}^{n} 1/(k - 1)` for `r ≥ 2` and `P_1 = 1/n`
(*Optimal Stopping and Applications*, Chapter 2, §2.1). The formula is defined for every `r`, but
it is a probability only for `1 ≤ r ≤ n`, the range of the results below: for `r = 0` it gives
`(1 - H_{n-1})/n` (negative for `n ≥ 4`), and for `r > n` it gives `1/n` although the rule then
selects no one. -/
noncomputable def winProb (n r : ℕ) : ℝ := (1 + ((r : ℝ) - 1) * harmonicTail n r) / n

/-- **Optimal threshold of the secretary problem.** `r₁ = min {r ≥ 1 : T_r ≤ 1}`, that is
`min {r ≥ 1 : ∑_{k=r+1}^{n} 1/(k - 1) ≤ 1}` (Ferguson, *Optimal Stopping and Applications*,
Chapter 2, equation (4)); the set contains `max n 1`. -/
noncomputable def optimalThreshold (n : ℕ) : ℕ :=
  Nat.find (⟨max n 1, le_max_right _ _, by simp [harmonicTail]⟩ :
    ∃ r, 1 ≤ r ∧ harmonicTail n r ≤ 1)

theorem one_le_optimalThreshold (n : ℕ) : 1 ≤ optimalThreshold n :=
  (Nat.find_spec (⟨max n 1, le_max_right _ _, by simp [harmonicTail]⟩ :
    ∃ r, 1 ≤ r ∧ harmonicTail n r ≤ 1)).1

theorem harmonicTail_optimalThreshold_le (n : ℕ) : harmonicTail n (optimalThreshold n) ≤ 1 :=
  (Nat.find_spec (⟨max n 1, le_max_right _ _, by simp [harmonicTail]⟩ :
    ∃ r, 1 ≤ r ∧ harmonicTail n r ≤ 1)).2

theorem one_lt_harmonicTail_of_lt_optimalThreshold {n r : ℕ} (hr : 1 ≤ r)
    (h : r < optimalThreshold n) : 1 < harmonicTail n r := by
  have := Nat.find_min (⟨max n 1, le_max_right _ _, by simp [harmonicTail]⟩ :
    ∃ r, 1 ≤ r ∧ harmonicTail n r ≤ 1) h
  exact lt_of_not_ge fun h' => this ⟨hr, h'⟩

theorem optimalThreshold_le {n : ℕ} (hn : 1 ≤ n) : optimalThreshold n ≤ n :=
  Nat.find_min' _ ⟨hn, by simp [harmonicTail]⟩

theorem harmonicTail_eq_add {n r : ℕ} (hrn : r < n) :
    harmonicTail n r = 1 / r + harmonicTail n (r + 1) := by
  unfold harmonicTail
  rw [Finset.sum_eq_sum_Ico_succ_bot hrn]

theorem harmonicTail_antitone (n : ℕ) {r s : ℕ} (hrs : r ≤ s) :
    harmonicTail n s ≤ harmonicTail n r := by
  unfold harmonicTail
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hrs) ?_
  intro j _ _
  positivity

/-- **Increment of the win probability of threshold rules** (Ferguson, *Optimal Stopping and
Applications*, Chapter 2, the computation before equation (4)): for `1 ≤ r < n`,
`P_{r+1} - P_r = (T_r - 1)/n`, so `P_{r+1} ≤ P_r` if and only if
`∑_{k=r+1}^{n} 1/(k - 1) ≤ 1`. -/
theorem winProb_succ_sub {n r : ℕ} (hr : 1 ≤ r) (hrn : r < n) :
    winProb n (r + 1) - winProb n r = (harmonicTail n r - 1) / n := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  unfold winProb
  rw [harmonicTail_eq_add hrn]
  push_cast
  field_simp
  ring


theorem winProb_le_succ_of_lt_optimalThreshold {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkr : k < optimalThreshold n) : winProb n k ≤ winProb n (k + 1) := by
  have hkn : k < n := hkr.trans_le (optimalThreshold_le hn)
  have hT := one_lt_harmonicTail_of_lt_optimalThreshold hk hkr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := winProb_succ_sub hk hkn
  have : 0 ≤ (harmonicTail n k - 1) / n := div_nonneg (by linarith) hn'.le
  linarith

theorem winProb_succ_le_of_optimalThreshold_le {n k : ℕ} (hk : optimalThreshold n ≤ k)
    (hkn : k < n) : winProb n (k + 1) ≤ winProb n k := by
  have hk1 : 1 ≤ k := (one_le_optimalThreshold n).trans hk
  have hT : harmonicTail n k ≤ 1 :=
    (harmonicTail_antitone n hk).trans (harmonicTail_optimalThreshold_le n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have := winProb_succ_sub hk1 hkn
  have : (harmonicTail n k - 1) / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hn'.le
  linarith

/-- **The optimal threshold rule of the secretary problem** (Ferguson, *Optimal Stopping and
Applications*, Chapter 2, equation (4)): for `n ≥ 1`, the threshold
`r₁ = min {r ≥ 1 : ∑_{k=r+1}^{n} 1/(k - 1) ≤ 1}` maximises the win probability `P_r` of the
threshold rules `N_r` over `1 ≤ r ≤ n`. -/
theorem winProb_le_winProb_optimalThreshold {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) :
    winProb n r ≤ winProb n (optimalThreshold n) := by
  rcases le_total r (optimalThreshold n) with h | h
  · have key : ∀ k, r ≤ k → k ≤ optimalThreshold n → winProb n r ≤ winProb n k := by
      intro k hrk
      induction k, hrk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hrk ih =>
        intro hk
        exact (ih (by omega)).trans
          (winProb_le_succ_of_lt_optimalThreshold hn (hr.trans hrk) (by omega))
    exact key _ h le_rfl
  · have key : ∀ k, optimalThreshold n ≤ k → k ≤ n →
        winProb n k ≤ winProb n (optimalThreshold n) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hk ih =>
        intro hkn
        exact (winProb_succ_le_of_optimalThreshold_le hk (by omega)).trans (ih (by omega))
    exact key _ h hrn

/-- **Integral lower bound for the harmonic tail.** For `1 ≤ r ≤ n`,
`log n - log r ≤ ∑_{j=r}^{n-1} 1/j`. -/
theorem log_sub_log_le_harmonicTail {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    Real.log n - Real.log r ≤ harmonicTail n r := by
  induction n, hrn using Nat.le_induction with
  | base => simp [harmonicTail]
  | succ n hrn ih =>
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hstep : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div (by positivity) hn.ne'] at h
      have : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    unfold harmonicTail at ih ⊢
    rw [Finset.sum_Ico_succ_top hrn]
    push_cast
    linarith

/-- **Integral upper bound for the harmonic tail.** For `2 ≤ r ≤ n`,
`∑_{j=r}^{n-1} 1/j ≤ log (n - 1) - log (r - 1)`. -/
theorem harmonicTail_le_log_sub_log {n r : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    harmonicTail n r ≤ Real.log ((n : ℝ) - 1) - Real.log ((r : ℝ) - 1) := by
  induction n, hrn using Nat.le_induction with
  | base => simp [harmonicTail]
  | succ n hrn ih =>
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hstep : 1 / (n : ℝ) ≤ Real.log n - Real.log ((n : ℝ) - 1) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < ((n : ℝ) - 1) / n by apply div_pos <;> linarith)
      rw [Real.log_div (by linarith) (by linarith)] at h
      have : ((n : ℝ) - 1) / n - 1 = -(1 / n) := by field_simp; ring
      linarith
    unfold harmonicTail at ih ⊢
    rw [Finset.sum_Ico_succ_top hrn]
    push_cast
    simp only [add_sub_cancel_right]
    linarith

theorem le_mul_optimalThreshold {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ Real.exp 1 * optimalThreshold n := by
  have hr := one_le_optimalThreshold n
  have hr' : (0 : ℝ) < optimalThreshold n := by exact_mod_cast hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (log_sub_log_le_harmonicTail hr (optimalThreshold_le hn)).trans
    (harmonicTail_optimalThreshold_le n)
  have : Real.log n ≤ Real.log (Real.exp 1 * optimalThreshold n) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hr'.ne', Real.log_exp]
    linarith
  exact (Real.log_le_log_iff hn' (by positivity)).mp this

theorem optimalThreshold_le_add_two {n : ℕ} (hn : 1 ≤ n) :
    (optimalThreshold n : ℝ) ≤ n / Real.exp 1 + 2 := by
  have he := Real.exp_pos 1
  rcases Nat.lt_or_ge (optimalThreshold n) 3 with h | h
  · have : (optimalThreshold n : ℝ) ≤ 2 := by exact_mod_cast (show optimalThreshold n ≤ 2 by omega)
    have : 0 ≤ (n : ℝ) / Real.exp 1 := by positivity
    linarith
  · set r := optimalThreshold n - 1 with hrdef
    have hr2 : 2 ≤ r := by omega
    have hrn : r ≤ n := by have := optimalThreshold_le hn; omega
    have h1 := one_lt_harmonicTail_of_lt_optimalThreshold (n := n) (show 1 ≤ r by omega)
      (show r < optimalThreshold n by omega)
    have h2 := harmonicTail_le_log_sub_log hr2 hrn
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      linarith
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast (hr2.trans hrn)
      linarith
    have hlog : Real.log (Real.exp 1 * ((r : ℝ) - 1)) < Real.log ((n : ℝ) - 1) := by
      rw [Real.log_mul he.ne' hr1.ne', Real.log_exp]
      linarith
    have hlt := (Real.log_lt_log_iff (by positivity) hn1).mp hlog
    have hcast : (optimalThreshold n : ℝ) = r + 1 := by
      rw [hrdef]; push_cast [show 1 ≤ optimalThreshold n from one_le_optimalThreshold n]; ring
    rw [hcast]
    have : ((r : ℝ) - 1) < ((n : ℝ) - 1) / Real.exp 1 := by
      rw [lt_div_iff₀ he]; linarith
    have : ((n : ℝ) - 1) / Real.exp 1 ≤ n / Real.exp 1 := by
      apply div_le_div_of_nonneg_right _ he.le; linarith
    linarith

/-- **The optimal threshold is asymptotically `n/e`** (Ferguson, *Optimal Stopping and
Applications*, Chapter 2, end of §2.1): `r₁(n)/n → 1/e` as `n → ∞`. -/
theorem tendsto_optimalThreshold_div :
    Tendsto (fun n : ℕ => (optimalThreshold n : ℝ) / n) atTop (𝓝 (Real.exp (-1))) := by
  have he := Real.exp_pos 1
  have hinv : Real.exp (-1) = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
  have hupper : Tendsto (fun n : ℕ => 1 / Real.exp 1 + 2 * (1 / (n : ℝ))) atTop
      (𝓝 (Real.exp (-1))) := by
    rw [hinv]
    simpa using (tendsto_one_div_atTop_nhds_zero_nat.const_mul 2).const_add (1 / Real.exp 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [hinv, div_le_div_iff₀ he hn', one_mul, mul_comm]
    exact le_mul_optimalThreshold hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := optimalThreshold_le_add_two hn
    rw [div_le_iff₀ hn']
    have : (1 / Real.exp 1 + 2 * (1 / (n : ℝ))) * n = n / Real.exp 1 + 2 := by
      field_simp
    linarith

/-- **The `1/e` law of the secretary problem** (Ferguson, *Optimal Stopping and Applications*,
Chapter 2, end of §2.1): the win probability of the optimal threshold rule tends to `1/e`,
`P_{r₁(n)} → 1/e` as `n → ∞`. -/
theorem tendsto_winProb_optimalThreshold :
    Tendsto (fun n : ℕ => winProb n (optimalThreshold n)) atTop (𝓝 (Real.exp (-1))) := by
  have hr := tendsto_optimalThreshold_div
  have hlower : Tendsto (fun n : ℕ => (optimalThreshold n : ℝ) / n - 1 / (n : ℝ)) atTop
      (𝓝 (Real.exp (-1))) := by
    simpa using hr.sub tendsto_one_div_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hr ?_ ?_
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have hn1 : 1 ≤ n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have h3 : 2 ≤ optimalThreshold n := by
      have h := le_mul_optimalThreshold hn1
      have he3 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      have h6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
      have : (2 : ℝ) < optimalThreshold n := by
        by_contra hc
        have hc' : (optimalThreshold n : ℝ) ≤ 2 := le_of_not_gt hc
        nlinarith [Real.exp_pos 1]
      exact_mod_cast this.le
    set r := optimalThreshold n with hrdef
    have hrn : r - 1 < n := by have := optimalThreshold_le hn1; omega
    have hT1 := one_lt_harmonicTail_of_lt_optimalThreshold (n := n) (show 1 ≤ r - 1 by omega)
      (show r - 1 < r by omega)
    rw [harmonicTail_eq_add hrn, show r - 1 + 1 = r by omega] at hT1
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by push_cast [show 1 ≤ r by omega]; ring
    rw [hcast] at hT1
    have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast h3
      linarith
    have hprod : (r : ℝ) - 2 < ((r : ℝ) - 1) * harmonicTail n r := by
      have h' : 1 - 1 / ((r : ℝ) - 1) < harmonicTail n r := by linarith
      have := mul_lt_mul_of_pos_left h' (show (0 : ℝ) < (r : ℝ) - 1 by linarith)
      rw [mul_sub, mul_one, mul_one_div_cancel (by linarith)] at this
      linarith
    unfold winProb
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hn']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hr1 : (0 : ℝ) ≤ (optimalThreshold n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ optimalThreshold n := by exact_mod_cast one_le_optimalThreshold n
      linarith
    have hT := harmonicTail_optimalThreshold_le n
    unfold winProb
    rw [div_le_div_iff_of_pos_right hn']
    nlinarith

end MathlibExt.Probability.Secretary
