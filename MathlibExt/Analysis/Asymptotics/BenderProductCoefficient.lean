/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Bender's product-coefficient asymptotic lemma

Proves `Wanted` entry `bender_product_coefficient_asymptotic`.
-/

open Filter

namespace MathlibExt.Analysis.Asymptotics.BenderProductCoefficient

@[expose] public section

-- Helper: product coefficients as a range sum.
private theorem bender_coeff_prod (a b : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)
      = ∑ k ∈ Finset.range (n + 1), a k * b (n - k) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k1 k2 => PowerSeries.coeff k1 (PowerSeries.mk a) *
        PowerSeries.coeff k2 (PowerSeries.mk b)) n]
  apply Finset.sum_congr rfl
  intro k hk
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

-- Helper: truncated subtraction tends to `atTop`.
private theorem bender_sub_tendsto_atTop (k : ℕ) : Tendsto (fun n : ℕ => n - k) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  exact ⟨b + k, fun n hn => by omega⟩

-- Helper: fixed-lag coefficient ratios tend to powers of the limit.
private theorem bender_ratio_pow (b : ℕ → ℝ) (β : ℝ)
    (hbnz : ∀ᶠ n in atTop, b n ≠ 0)
    (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds β)) (k : ℕ) :
    Tendsto (fun n => b (n - k) / b n) atTop (nhds (β ^ k)) := by
  induction k with
  | zero =>
    simp only [Nat.sub_zero, pow_zero]
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hbnz] with n hn
    simp [hn]
  | succ k ih =>
    have hcomp : Tendsto (fun n : ℕ => b ((n - k) - 1) / b (n - k)) atTop (nhds β) :=
      hratio.comp (bender_sub_tendsto_atTop k)
    have hmul := hcomp.mul ih
    rw [← pow_succ'] at hmul
    refine hmul.congr' ?_
    filter_upwards [(bender_sub_tendsto_atTop k).eventually hbnz] with n hn
    rw [Nat.sub_sub]
    rw [div_mul_div_comm]
    rw [mul_comm (b (n - k)) (b n)]
    rw [mul_div_mul_right _ _ hn]

-- Helper: an intermediate radius strictly between `β` and `α`.
private theorem bender_exists_intermediate_radius (β : NNReal) (α : ENNReal)
    (h : ENNReal.ofNNReal β < α) :
    ∃ r : NNReal, β < r ∧ ENNReal.ofNNReal r < α := by
  rcases eq_or_ne α ⊤ with rfl | hα
  · refine ⟨β + 1, lt_add_of_pos_right _ zero_lt_one, ?_⟩
    simp
  · lift α to NNReal using hα
    rw [ENNReal.coe_lt_coe] at h
    obtain ⟨r, hβr, hrα⟩ := exists_between h
    exact ⟨r, hβr, by exact_mod_cast hrα⟩

-- Helper: eventual absolute bound on consecutive coefficient ratios.
private theorem bender_ratio_eventually_bounded (b : ℕ → ℝ) (β s : ℝ) (hβ : 0 ≤ β) (hβs : β < s)
    (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds β)) :
    ∀ᶠ n in atTop, |b (n - 1) / b n| ≤ s := by
  have hdist : ∀ᶠ n in atTop, dist (b (n - 1) / b n) β < s - β :=
    hratio.eventually (Metric.ball_mem_nhds β (by linarith))
  filter_upwards [hdist] with n hn
  rw [Real.dist_eq] at hn
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hn
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

-- Helper: absolute summability of `a` at any radius below `α`.
private theorem bender_summable_norm_a (a : ℕ → ℝ) (α : ENNReal) (s : NNReal)
    (hA : (FormalMultilinearSeries.ofScalars ℝ a).radius = α)
    (hs : ENNReal.ofNNReal s < α) :
    Summable (fun n => ‖a n‖ * (s : ℝ) ^ n) := by
  have hs' : (s : ENNReal) < (FormalMultilinearSeries.ofScalars ℝ a).radius := by
    rw [hA]; exact hs
  have hsum := FormalMultilinearSeries.summable_norm_mul_pow
    (FormalMultilinearSeries.ofScalars ℝ a) hs'
  simp only [FormalMultilinearSeries.ofScalars_norm] at hsum
  exact hsum

-- Helper: telescoping product bound while the index stays above `N1`.
private theorem bender_telescope_bound (b : ℕ → ℝ) (r : ℝ) (N1 : ℕ) (hr : 0 ≤ r)
    (hbd : ∀ m, N1 ≤ m → |b (m - 1) / b m| ≤ r)
    (hbn : ∀ m, N1 ≤ m → b m ≠ 0)
    (n k : ℕ) (hn : N1 ≤ n) (hkn : k ≤ n - N1) :
    |b (n - k) / b n| ≤ r ^ k := by
  induction k generalizing n with
  | zero =>
    simp only [Nat.sub_zero, pow_zero]
    rw [div_self (hbn n hn)]
    simp
  | succ k ih =>
    have hk_le : k ≤ n - N1 := by omega
    have hm_ge : N1 ≤ n - k := by omega
    have hbnk : b (n - k) ≠ 0 := hbn (n - k) hm_ge
    have hstep : b (n - (k + 1)) / b n
        = (b ((n - k) - 1) / b (n - k)) * (b (n - k) / b n) := by
      have hnk : n - (k + 1) = (n - k) - 1 := by omega
      rw [hnk]
      rw [div_mul_div_cancel₀ hbnk]
    rw [hstep]
    calc |(b ((n - k) - 1) / b (n - k)) * (b (n - k) / b n)|
        ≤ |b ((n - k) - 1) / b (n - k)| * |b (n - k) / b n| := (abs_mul _ _).le
      _ ≤ r * r ^ k := by
          apply mul_le_mul (hbd (n - k) hm_ge) (ih n hn hk_le)
          · exact abs_nonneg _
          · exact hr
      _ = r ^ (k + 1) := by rw [pow_succ']

-- Helper: geometric lower bound on `|b n|` from the eventual ratio bound.
private theorem bender_abs_lower_bound (b : ℕ → ℝ) (r : ℝ) (N1 : ℕ) (hr : 0 < r)
    (hbd : ∀ m, N1 ≤ m → |b (m - 1) / b m| ≤ r)
    (hbn : ∀ m, N1 ≤ m → b m ≠ 0)
    (n : ℕ) (hn : N1 ≤ n) :
    |b N1| ≤ |b n| * r ^ (n - N1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hm1 : N1 ≤ m + 1 := by omega
    have hmem : (m + 1) - 1 = m := by omega
    have hratio : |b m| ≤ r * |b (m + 1)| := by
      have h := hbd (m + 1) hm1
      rw [hmem] at h
      rw [abs_div] at h
      have hbpos : (0:ℝ) < |b (m + 1)| := abs_pos.mpr (hbn (m + 1) hm1)
      have hbm : |b m| / |b (m + 1)| ≤ r := h
      calc |b m| = (|b m| / |b (m + 1)|) * |b (m + 1)| := by
              field_simp
        _ ≤ r * |b (m + 1)| := by
              apply mul_le_mul_of_nonneg_right h (le_of_lt hbpos)
    have hexp : m + 1 - N1 = (m - N1) + 1 := by omega
    calc |b N1| ≤ |b m| * r ^ (m - N1) := ih
      _ ≤ (r * |b (m + 1)|) * r ^ (m - N1) := by
          apply mul_le_mul_of_nonneg_right hratio (pow_nonneg (le_of_lt hr) _)
      _ = |b (m + 1)| * r ^ (m + 1 - N1) := by
          rw [hexp, pow_succ']
          ring

-- Helper: uniform bound `|b (n-k) / b n| ≤ C * r ^ k` for all `k ≤ n`, `n ≥ N1`.
private theorem bender_uniform_bound (b : ℕ → ℝ) (r : ℝ) (N1 : ℕ) (hr : 0 < r)
    (hbd : ∀ m, N1 ≤ m → |b (m - 1) / b m| ≤ r)
    (hbn : ∀ m, N1 ≤ m → b m ≠ 0)
    (hbN1 : b N1 ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ 1 ≤ C ∧
      ∀ n, N1 ≤ n → ∀ k, k ≤ n → |b (n - k) / b n| ≤ C * r ^ k := by
  have hrnn : 0 ≤ r := le_of_lt hr
  have hbN1pos : (0:ℝ) < |b N1| := abs_pos.mpr hbN1
  have hrN1pos : (0:ℝ) < r ^ N1 := pow_pos hr N1
  -- Majorant for the finitely many early coefficients.
  set M : ℝ := ∑ j ∈ Finset.range N1, |b j| with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hMbound : ∀ j, j < N1 → |b j| ≤ M := by
    intro j hj
    have hmem : j ∈ Finset.range N1 := Finset.mem_range.mpr hj
    exact Finset.single_le_sum (fun i _ => abs_nonneg (b i)) hmem
  -- Constant dominating both regimes.
  set A1 : ℝ := M * (|b N1|)⁻¹ with hA1
  set A2 : ℝ := M * (|b N1|)⁻¹ * (r ^ N1)⁻¹ with hA2
  have hA1nn : 0 ≤ A1 := by
    rw [hA1]
    apply mul_nonneg hMnn (inv_nonneg.mpr (le_of_lt hbN1pos))
  have hA2nn : 0 ≤ A2 := by
    rw [hA2]
    apply mul_nonneg hA1nn (inv_nonneg.mpr (le_of_lt hrN1pos))
  refine ⟨A1 + A2 + 1, by positivity, by linarith, ?_⟩
  intro n hn k hk
  have hbn_n : b n ≠ 0 := hbn n hn
  have hnpos : (0:ℝ) < |b n| := abs_pos.mpr hbn_n
  have hrk_nn : (0:ℝ) ≤ r ^ k := pow_nonneg hrnn k
  have hC1 : A1 ≤ A1 + A2 + 1 := by linarith
  have hC2 : A2 ≤ A1 + A2 + 1 := by linarith
  have h1C : (1:ℝ) ≤ A1 + A2 + 1 := by linarith
  by_cases hcase : n - k < N1
  · -- Early-index regime: numerator is one of finitely many values.
    have hj_lt : n - k < N1 := hcase
    have hnum : |b (n - k)| ≤ M := hMbound (n - k) hj_lt
    have hlow := bender_abs_lower_bound b r N1 hr hbd hbn n hn
    -- `1 / |b n| ≤ r ^ (n - N1) / |b N1|`.
    have hinv : (1:ℝ) / |b n| ≤ r ^ (n - N1) / |b N1| := by
      rw [le_div_iff₀ hbN1pos]
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hnpos]
      calc |b N1| ≤ |b n| * r ^ (n - N1) := hlow
        _ = r ^ (n - N1) * |b n| := mul_comm _ _
    have hdiv : |b (n - k) / b n| ≤ M * (r ^ (n - N1) / |b N1|) := by
      rw [abs_div]
      calc |b (n - k)| / |b n| = |b (n - k)| * (1 / |b n|) := by ring
        _ ≤ M * (r ^ (n - N1) / |b N1|) := by
            apply mul_le_mul hnum hinv (by positivity) (by positivity)
    -- Reduce to `r ^ n ≤ r ^ k * r ^ N1` when `r ≤ 1`, else direct.
    by_cases hr1 : 1 ≤ r
    · have hle : n - N1 ≤ k := by omega
      have hpow : r ^ (n - N1) ≤ r ^ k := pow_le_pow_right₀ hr1 hle
      calc |b (n - k) / b n| ≤ M * (r ^ (n - N1) / |b N1|) := hdiv
        _ = A1 * r ^ (n - N1) := by rw [hA1]; ring
        _ ≤ A1 * r ^ k := by
            apply mul_le_mul_of_nonneg_left hpow hA1nn
        _ ≤ (A1 + A2 + 1) * r ^ k := by
            apply mul_le_mul_of_nonneg_right _ hrk_nn
            linarith
    · push Not at hr1
      have hrle : r ≤ 1 := le_of_lt hr1
      have hkn : k ≤ n := hk
      have hpow : r ^ n ≤ r ^ k := pow_le_pow_of_le_one hrnn hrle hkn
      have hN1n : N1 ≤ n := hn
      have hnsplit : r ^ n = r ^ N1 * r ^ (n - N1) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hN1n, pow_add]
      have hkey : r ^ (n - N1) ≤ (r ^ N1)⁻¹ * r ^ k := by
        have hpos : (0:ℝ) < r ^ N1 := hrN1pos
        rw [le_inv_mul_iff₀ hpos]
        calc r ^ N1 * r ^ (n - N1) = r ^ (N1 + (n - N1)) := by rw [pow_add]
          _ = r ^ n := by rw [Nat.add_sub_cancel' hN1n]
          _ ≤ r ^ k := hpow
      calc |b (n - k) / b n| ≤ M * (r ^ (n - N1) / |b N1|) := hdiv
        _ = (M * (|b N1|)⁻¹) * r ^ (n - N1) := by ring
        _ ≤ (M * (|b N1|)⁻¹) * ((r ^ N1)⁻¹ * r ^ k) := by
            apply mul_le_mul_of_nonneg_left hkey
            apply mul_nonneg hMnn (inv_nonneg.mpr (le_of_lt hbN1pos))
        _ = A2 * r ^ k := by rw [hA2]; ring
        _ ≤ (A1 + A2 + 1) * r ^ k := by
            apply mul_le_mul_of_nonneg_right _ hrk_nn
            linarith
  · -- Telescoping regime: all ratios in the product are bounded by `r`.
    push Not at hcase
    have hkn : k ≤ n - N1 := by omega
    have htel := bender_telescope_bound b r N1 hrnn hbd hbn n k hn hkn
    calc |b (n - k) / b n| ≤ r ^ k := htel
      _ = 1 * r ^ k := (one_mul _).symm
      _ ≤ (A1 + A2 + 1) * r ^ k := by
          apply mul_le_mul_of_nonneg_right _ hrk_nn
          linarith

/-- **Bender's lemma without a radius condition on the second series.** Let $(a_n)$ and $(b_n)$
be real sequences, let $A(z) = \sum_n a_n z^n$ have radius of convergence $\alpha \in [0, \infty]$,
and let $\beta \ge 0$ be a real number with $\beta < \alpha$. Suppose that $b_n \neq 0$ for all
sufficiently large $n$, that $b_{n-1} / b_n \to \beta$ as $n \to \infty$, and that
$A(\beta) \neq 0$. Then the coefficients $c_n = \sum_{k=0}^{n} a_k b_{n-k}$ of the product of the
formal power series $\sum_n a_n z^n$ and $\sum_n b_n z^n$ satisfy $c_n \sim A(\beta) \, b_n$ as
$n \to \infty$.

Unlike Bender's original lemma, nothing is assumed about the radius of convergence of
$\sum_n b_n z^n$. -/
theorem bender_product_coefficient_asymptotic_general
    (a b : ℕ → ℝ) (α : ENNReal) (β : NNReal)
    (hA : (FormalMultilinearSeries.ofScalars ℝ a).radius = α)
    (hαβ : ENNReal.ofNNReal β < α)
    (hbnz : ∀ᶠ n in atTop, b n ≠ 0)
    (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds (β : ℝ)))
    (hAβ : FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) ≠ 0) :
    Asymptotics.IsEquivalent atTop
      (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b))
      (fun n => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n) := by
  -- Reduce to showing the quotient tends to 1.
  apply Asymptotics.isEquivalent_of_tendsto_one
  -- Rewrite the numerator as an explicit convolution sum.
  have hrewrite : (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b)) /
      (fun n => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n)
      = (fun n => (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) /
        (FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n)) := by
    funext n
    simp only [Pi.div_apply]
    rw [bender_coeff_prod]
  rw [hrewrite]
  -- Dominated-convergence setup: intermediate radius, summable majorant,
  -- and an eventual absolute bound on consecutive `b`-ratios.
  obtain ⟨r, hβr, hrα⟩ := bender_exists_intermediate_radius β α hαβ
  have hsumm : Summable (fun n => ‖a n‖ * (r : ℝ) ^ n) :=
    bender_summable_norm_a a α r hA hrα
  have hβr_real : (β : ℝ) < (r : ℝ) := by exact_mod_cast hβr
  have hbound : ∀ᶠ n in atTop, |b (n - 1) / b n| ≤ (r : ℝ) :=
    bender_ratio_eventually_bounded b (β : ℝ) (r : ℝ)
      (by positivity : (0:ℝ) ≤ (β:ℝ)) hβr_real hratio
  -- Remaining goal: the normalized convolution sum tends to 1 via dominated convergence.
  -- Get a uniform threshold `N1` for the ratio bound and nonvanishing.
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (hbound.and hbnz)
  have hbd : ∀ m, N1 ≤ m → |b (m - 1) / b m| ≤ (r : ℝ) := fun m hm => (hN1 m hm).1
  have hbn : ∀ m, N1 ≤ m → b m ≠ 0 := fun m hm => (hN1 m hm).2
  have hbN1 : b N1 ≠ 0 := hbn N1 le_rfl
  have hrpos : (0:ℝ) < (r : ℝ) := by
    calc (0:ℝ) ≤ (β : ℝ) := by positivity
      _ < (r : ℝ) := hβr_real
  obtain ⟨C, hCnn, hC1, hC⟩ := bender_uniform_bound b (r : ℝ) N1 hrpos hbd hbn hbN1
  -- Identify `S` with its `tsum`.
  have hS_tsum : FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ)
      = ∑' k, a k * (β : ℝ) ^ k := by
    have h := FormalMultilinearSeries.ofScalarsSum_eq_tsum (𝕜 := ℝ) (E := ℝ) a
    simp only [h]
    apply tsum_congr
    intro k
    rw [smul_eq_mul]
  -- Summability of the limit and the majorant.
  have hsummβ : Summable (fun k => ‖a k‖ * (β : ℝ) ^ k) :=
    bender_summable_norm_a a α β hA hαβ
  have hsum_lim : Summable (fun k => a k * (β : ℝ) ^ k) := by
    apply Summable.of_norm
    have : (fun k => ‖a k * (β : ℝ) ^ k‖) = (fun k => ‖a k‖ * (β : ℝ) ^ k) := by
      funext k
      rw [norm_mul, norm_pow]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (β : ℝ))]
    rw [this]
    exact hsummβ
  have hbound_summ : Summable (fun k => C * (‖a k‖ * (r : ℝ) ^ k)) :=
    hsumm.mul_left C
  -- Dominated family.
  set F : ℕ → ℕ → ℝ := fun n k => if k ≤ n then a k * (b (n - k) / b n) else 0 with hF
  set G : ℕ → ℝ := fun k => a k * (β : ℝ) ^ k with hG
  have hpoint : ∀ k, Tendsto (fun n => F n k) atTop (nhds (G k)) := by
    intro k
    have hlim : Tendsto (fun n => a k * (b (n - k) / b n)) atTop (nhds (a k * (β : ℝ) ^ k)) :=
      tendsto_const_nhds.mul (bender_ratio_pow b (β : ℝ) hbnz hratio k)
    apply hlim.congr'
    filter_upwards [Filter.eventually_atTop.mpr ⟨k, fun n hn => hn⟩] with n hn
    simp only [hF, hn, ↓reduceIte]
  have hdom : ∀ᶠ n in atTop, ∀ k, ‖F n k‖ ≤ C * (‖a k‖ * (r : ℝ) ^ k) := by
    filter_upwards [Filter.eventually_atTop.mpr ⟨N1, fun n hn => hn⟩] with n hn k
    simp only [hF]
    by_cases hk : k ≤ n
    · simp only [hk, ↓reduceIte]
      rw [norm_mul]
      calc ‖a k‖ * ‖b (n - k) / b n‖
          ≤ ‖a k‖ * (C * (r : ℝ) ^ k) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            calc ‖b (n - k) / b n‖ = |b (n - k) / b n| := Real.norm_eq_abs _
              _ ≤ C * (r : ℝ) ^ k := hC n hn k (by omega)
        _ = C * (‖a k‖ * (r : ℝ) ^ k) := by ring
    · simp only [hk, ↓reduceIte]
      simp only [norm_zero]
      apply mul_nonneg hCnn
      apply mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hrpos) _)
  have htsum : Tendsto (fun n => ∑' k, F n k) atTop
      (nhds (∑' k, G k)) :=
    tendsto_tsum_of_dominated_convergence hbound_summ hpoint hdom
  have htsum_eq : (∑' k, G k) = FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) := by
    simp only [hG]
    rw [← hS_tsum]
  rw [htsum_eq] at htsum
  -- Each `tsum` is the normalized partial sum.
  have hFn_eq : ∀ᶠ n in atTop, (∑' k, F n k)
      = (∑ k ∈ Finset.range (n + 1), a k * b (n - k)) / b n := by
    filter_upwards [hbnz] with n hn
    have hsupp : ∀ k, k ∉ Finset.range (n + 1) → F n k = 0 := by
      intro k hk
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hk' : ¬k ≤ n := by omega
      simp only [hF, hk', ↓reduceIte]
    have hts : (∑' k, F n k) = ∑ k ∈ Finset.range (n + 1), F n k := tsum_eq_sum hsupp
    rw [hts]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    simp only [hF, hk, ↓reduceIte]
    field_simp
  -- Divide by `S` to get the goal.
  have hQ : Tendsto ((fun n => (∑' k, F n k))
      / (fun _ => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ)))
      atTop (nhds 1) := by
    have hdiv := htsum.div tendsto_const_nhds hAβ
    simpa [div_self hAβ] using hdiv
  apply hQ.congr'
  filter_upwards [hFn_eq, hbnz] with n hFn hn
  simp only [Pi.div_apply]
  rw [hFn]
  field_simp

set_option linter.unusedVariables false in
/-- **Bender's lemma on coefficients of a product of power series.** Let $(a_n)$ and $(b_n)$ be
real sequences such that $A(z) = \sum_n a_n z^n$ has radius of convergence $\alpha \in [0, \infty]$
and $\sum_n b_n z^n$ has radius of convergence $\beta$, where $\beta \ge 0$ is a real number with
$\beta < \alpha$. Suppose that $b_n \neq 0$ for all sufficiently large $n$, that
$b_{n-1} / b_n \to \beta$ as $n \to \infty$, and that $A(\beta) \neq 0$. Then the coefficients
$c_n = \sum_{k=0}^{n} a_k b_{n-k}$ of the product of the formal power series $\sum_n a_n z^n$ and
$\sum_n b_n z^n$ satisfy $c_n \sim A(\beta) \, b_n$ as $n \to \infty$.

The hypothesis that $b_n$ is eventually nonzero makes the ratios $b_{n-1} / b_n$ meaningful; with
the convention $x / 0 = 0$ the statement fails at $\beta = 0$ without it: for $A(z) = 1 + z$ and
$b$ vanishing at every even index and growing fast at odd indices, every ratio is $0$ while the
even product coefficients stay nonzero.

Source: Dennis E. Davenport, Louis W. Shapiro, Lara K. Pudwell, and Leon C. Woodson,
"The Boundary of Ordered Trees," Journal of Integer Sequences 18 (2015).
Source file: `https://cs.uwaterloo.ca/journals/JIS/VOL18/Davenport/dav3.tex`
(Bender's lemma, lines 521-523).
File SHA-256: `32a240baaed6ae2300ec1302ccf7d3cd50dc1976868c161f0029c77d0d43b845`.
Span SHA-256 (LF joining, no terminal LF):
`665087b645846d87aadb08ae26e311b6d717dd5340e113e601cacab26f1c0d85`.
Concept: `jis_grounded_6fda7dab32c4f4ae24158c9e`
(dependency `jis_dep_2479eb9e033e69c0a770ff11`).
It follows from `bender_product_coefficient_asymptotic_general`; the hypothesis `hB` is unused and
keeps the source's shape.
Proves `Wanted` entry `bender_product_coefficient_asymptotic`.
-/
theorem bender_product_coefficient_asymptotic
    (a b : ℕ → ℝ) (α : ENNReal) (β : NNReal)
    (hA : (FormalMultilinearSeries.ofScalars ℝ a).radius = α)
    (hB : (FormalMultilinearSeries.ofScalars ℝ b).radius = ENNReal.ofNNReal β)
    (hαβ : ENNReal.ofNNReal β < α)
    (hbnz : ∀ᶠ n in atTop, b n ≠ 0)
    (hratio : Tendsto (fun n => b (n - 1) / b n) atTop (nhds (β : ℝ)))
    (hAβ : FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) ≠ 0) :
    Asymptotics.IsEquivalent atTop
      (fun n => PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk b))
      (fun n => FormalMultilinearSeries.ofScalarsSum (E := ℝ) a (β : ℝ) * b n) :=
  bender_product_coefficient_asymptotic_general a b α β hA hαβ hbnz hratio hAβ

end

end MathlibExt.Analysis.Asymptotics.BenderProductCoefficient
