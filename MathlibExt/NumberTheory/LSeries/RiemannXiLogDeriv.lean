/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.RiemannXiZeros
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros
import MathlibExt.NumberTheory.LSeries.ZeroCounting

/-!
# Bounds for `ξ'/ξ`

Bounds for the logarithmic derivative of the Riemann `ξ` function, used to estimate the horizontal
sides of contours in the explicit formulas of Weil and Landau.

## Main statements

* `RiemannXi.exists_norm_logDeriv_riemannXi_le`: `ξ'/ξ(w) = O(log |w|)` on `Re w ≥ 1 + δ`.
* `RiemannXi.exists_good_height_norm_logDeriv_riemannXi_le`: every large height can be moved by
  at most `1` to a height `T'` where `ξ'/ξ(σ ± iT') = O(log² T')` for `-ε ≤ σ ≤ 1 + ε`.
-/

@[expose] public section

open Complex

namespace RiemannXi

/-- `ξ'/ξ(w) = O(log |w|)` on every half-plane `Re w ≥ 1 + δ`. -/
theorem exists_norm_logDeriv_riemannXi_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ w : ℂ, 1 + δ ≤ w.re → ‖logDeriv riemannXi w‖ ≤ K + Real.log (‖w‖ + 1) := by
  obtain ⟨Kζ, -, hKζ⟩ := exists_norm_logDeriv_riemannZeta_le hδ
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_le_log_add
  refine ⟨Kζ + 1 / δ + |Real.log Real.pi| / 2 + |Cψ| / 2, fun w hw => ?_⟩
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw; linarith
  have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [logDeriv_riemannXi_eq hw1 hζ]
  have hure : (w / 2 + 1).re = w.re / 2 + 1 := by simp
  have hu1 : 1 ≤ ‖w / 2 + 1‖ := le_trans (by rw [hure]; linarith) (re_le_norm _)
  have hun : ‖w / 2 + 1‖ ≤ ‖w‖ + 1 := by
    calc ‖w / 2 + 1‖ ≤ ‖w / 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖w‖ + 1 := by rw [norm_div]; simp
  have hψ := hCψ _ (by rw [hure]; linarith) hu1
  have hlogu : Real.log ‖w / 2 + 1‖ ≤ Real.log (‖w‖ + 1) := Real.log_le_log (by linarith) hun
  have hlog0 : 0 ≤ Real.log ‖w / 2 + 1‖ := Real.log_nonneg hu1
  have hinv : ‖1 / (w - 1)‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le hδ
    calc δ ≤ (w - 1).re := by simp; linarith
      _ ≤ ‖w - 1‖ := re_le_norm _
  have hlp : ‖(Real.log Real.pi : ℂ) / 2‖ = |Real.log Real.pi| / 2 := by
    rw [norm_div, norm_real]; simp
  have hdg : ‖digamma (w / 2 + 1) / 2‖ = ‖digamma (w / 2 + 1)‖ / 2 := by
    rw [norm_div]; simp
  have hKw : ‖logDeriv riemannZeta w‖ ≤ Kζ := by rw [logDeriv_apply]; exact hKζ w hw
  have hC := le_abs_self Cψ
  calc ‖logDeriv riemannZeta w + (1 / (w - 1) - (Real.log Real.pi : ℂ) / 2 +
        digamma (w / 2 + 1) / 2)‖
      ≤ ‖logDeriv riemannZeta w‖ + (‖1 / (w - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
          ‖digamma (w / 2 + 1) / 2‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by rw [hlp, hdg]; linarith

/-- **Good heights for `ξ'/ξ`.** For `ε > 0`, every large height `T` can be moved by at most `1`
to a height `T' ≥ 2` that is not the absolute value of the ordinate of a nontrivial zero of `ζ` and
on which `‖ξ'/ξ(σ ± iT')‖ ≤ K log² T'` for `-ε ≤ σ ≤ 1 + ε`. -/
theorem exists_good_height_norm_logDeriv_riemannXi_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K T₁ : ℝ, 0 < T₁ ∧ ∀ T ≥ T₁, ∃ T' : ℝ, |T' - T| ≤ 1 ∧ 2 ≤ T' ∧
      (∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ T') ∧
      ∀ σ : ℝ, -ε ≤ σ → σ ≤ 1 + ε →
        ‖logDeriv riemannXi ((σ : ℂ) + (T' : ℂ) * I)‖ ≤ K * Real.log T' ^ 2 ∧
        ‖logDeriv riemannXi ((σ : ℂ) - (T' : ℂ) * I)‖ ≤ K * Real.log T' ^ 2 := by
  obtain ⟨Cg, T₀, hg⟩ := exists_good_height_norm_logDeriv_riemannZeta_le
  obtain ⟨KA, hKA⟩ := exists_norm_logDeriv_riemannXi_le one_pos
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_le_log_add
  refine ⟨|Cg| + 4 + |Cψ| + |KA| + Real.log (3 + ε) + 1, max T₀ 6, by positivity,
    fun T hT => ?_⟩
  obtain ⟨T', hT'1, hord, hζb⟩ := hg T (le_trans (le_max_left _ _) hT)
  have hT'5 : 5 ≤ T' := by rw [abs_le] at hT'1; linarith [le_max_right T₀ 6]
  have hlog1 : 1 ≤ Real.log T' := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hlog2 : Real.log T' ≤ Real.log T' ^ 2 := by nlinarith
  have hl3 : 0 ≤ Real.log (3 + ε) := Real.log_nonneg (by linarith)
  have hpi4 := Real.pi_le_four
  have hpi2 := Real.two_le_pi
  have htop : ∀ σ : ℝ, -ε ≤ σ → σ ≤ 1 + ε →
      ‖logDeriv riemannXi ((σ : ℂ) + (T' : ℂ) * I)‖ ≤
        (|Cg| + 4 + |Cψ| + |KA| + Real.log (3 + ε) + 1) * Real.log T' ^ 2 := by
    intro σ hσ1 hσ2
    set w : ℂ := (σ : ℂ) + (T' : ℂ) * I with hw
    have hwre : w.re = σ := by simp [hw]
    have hwim : w.im = T' := by simp [hw]
    have hξ : riemannXi w ≠ 0 := fun h => hord w ((riemannXi_eq_zero_iff w).mp h) hwim
    have hwn : ‖w‖ ≤ 1 + ε + T' := by
      calc ‖w‖ ≤ |w.re| + |w.im| := norm_le_abs_re_add_abs_im _
        _ ≤ 1 + ε + T' := by
          rw [hwre, hwim, abs_of_pos (by linarith : (0:ℝ) < T')]
          have : |σ| ≤ 1 + ε := abs_le.mpr ⟨by linarith, hσ2⟩
          linarith
    by_cases hmid : -1 ≤ σ ∧ σ ≤ 2
    · have hw1 : w ≠ 1 := fun h => by rw [h] at hwim; simp at hwim; linarith
      have hζ : riemannZeta w ≠ 0 := fun h0 =>
        hξ (riemannXi_eq_zero_of_riemannZeta_eq_zero (by rw [hwim]; linarith) h0)
      rw [logDeriv_riemannXi_eq hw1 hζ]
      have hζw : ‖logDeriv riemannZeta w‖ ≤ Cg * Real.log T' ^ 2 := by
        rw [logDeriv_apply]; exact hζb σ hmid.1 hmid.2
      have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (sub_ne_zero.mpr hw1))]
        calc (1 : ℝ) ≤ |(w - 1).im| := by
              rw [sub_im, hwim, one_im, sub_zero, abs_of_pos (by linarith)]; linarith
          _ ≤ ‖w - 1‖ := abs_im_le_norm _
      have hlp : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ 2 := by
        rw [norm_div, norm_real]
        have h0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
        have h1 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos (by linarith)
        simp only [Real.norm_eq_abs, abs_of_nonneg h0]
        norm_num
        linarith
      have hure : (w / 2 + 1).re = σ / 2 + 1 := by simp [hwre]
      have huim : (w / 2 + 1).im = T' / 2 := by simp [hwim]
      have hu1 : 1 ≤ ‖w / 2 + 1‖ := by
        calc (1 : ℝ) ≤ |(w / 2 + 1).im| := by rw [huim, abs_of_pos (by linarith)]; linarith
          _ ≤ _ := abs_im_le_norm _
      have hun : ‖w / 2 + 1‖ ≤ T' := by
        calc ‖w / 2 + 1‖ ≤ |(w / 2 + 1).re| + |(w / 2 + 1).im| := norm_le_abs_re_add_abs_im _
          _ ≤ T' := by
            rw [hure, huim, abs_of_pos (by linarith : (0:ℝ) < T' / 2)]
            have : |σ / 2 + 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
            linarith
      have hψ := hCψ _ (by rw [hure]; linarith) hu1
      have hlogu : Real.log ‖w / 2 + 1‖ ≤ Real.log T' := Real.log_le_log (by linarith) hun
      have hdg : ‖digamma (w / 2 + 1) / 2‖ = ‖digamma (w / 2 + 1)‖ / 2 := by
        rw [norm_div]; simp
      have htri : ‖logDeriv riemannZeta w + (1 / (w - 1) - (Real.log Real.pi : ℂ) / 2 +
          digamma (w / 2 + 1) / 2)‖
          ≤ ‖logDeriv riemannZeta w‖ + (‖1 / (w - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖digamma (w / 2 + 1) / 2‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      rw [hdg] at htri
      have hCg : Cg * Real.log T' ^ 2 ≤ |Cg| * Real.log T' ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have hsq0 : 0 ≤ Real.log T' ^ 2 := by positivity
      have hK1 : |Cψ| * 1 ≤ |Cψ| * Real.log T' ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have hK2 : 0 ≤ (|KA| + Real.log (3 + ε) + 1) * Real.log T' ^ 2 := by positivity
      have habs := le_abs_self Cψ
      have habs' := abs_nonneg Cψ
      have hexp : (|Cg| + 4 + |Cψ| + |KA| + Real.log (3 + ε) + 1) * Real.log T' ^ 2 =
          |Cg| * Real.log T' ^ 2 + 4 * Real.log T' ^ 2 + |Cψ| * Real.log T' ^ 2 +
            (|KA| + Real.log (3 + ε) + 1) * Real.log T' ^ 2 := by ring
      rw [hexp]
      linarith
    · have hcase : ‖logDeriv riemannXi w‖ ≤ KA + Real.log (‖w‖ + 2) := by
        rcases not_and_or.mp hmid with h | h
        · simp only [not_le] at h
          have h1w : 1 + 1 ≤ (1 - w).re := by simp [hwre]; linarith
          have e : logDeriv riemannXi w = -logDeriv riemannXi (1 - w) := by
            have := logDeriv_riemannXi_one_sub (1 - w)
            rw [sub_sub_cancel] at this
            exact this
          rw [e, norm_neg]
          have hb := hKA (1 - w) h1w
          have hn : ‖1 - w‖ + 1 ≤ ‖w‖ + 2 := by
            have := norm_sub_le (1 : ℂ) w
            simp at this; linarith
          have := Real.log_le_log (by positivity) hn
          linarith
        · simp only [not_le] at h
          have hb := hKA w (by rw [hwre]; linarith)
          have := Real.log_le_log (by positivity) (by linarith : ‖w‖ + 1 ≤ ‖w‖ + 2)
          linarith
      have hlw : Real.log (‖w‖ + 2) ≤ Real.log (3 + ε) + Real.log T' := by
        rw [← Real.log_mul (by linarith) (by linarith)]
        apply Real.log_le_log (by positivity)
        nlinarith
      have hsq0 : 0 ≤ Real.log T' ^ 2 := by positivity
      have hK1 : (|KA| + Real.log (3 + ε)) * 1 ≤ (|KA| + Real.log (3 + ε)) * Real.log T' ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hK2 : (|Cg| + 4 + |Cψ|) * 0 ≤ (|Cg| + 4 + |Cψ|) * Real.log T' ^ 2 :=
        mul_le_mul_of_nonneg_left hsq0 (by positivity)
      have := le_abs_self KA
      nlinarith
  have habs : ∀ ρ ∈ riemannZetaNontrivialZeros, |ρ.im| ≠ T' := by
    intro ρ hρ h
    rcases (abs_eq (by linarith : (0 : ℝ) ≤ T')).mp h with h1 | h1
    · exact hord ρ hρ h1
    · exact hord _ (conj_mem_riemannZetaNontrivialZeros hρ) (by rw [Complex.conj_im, h1, neg_neg])
  refine ⟨T', hT'1, by linarith, habs, fun σ hσ1 hσ2 => ⟨htop σ hσ1 hσ2, ?_⟩⟩
  have e : (σ : ℂ) - (T' : ℂ) * I = 1 - (((1 - σ : ℝ) : ℂ) + (T' : ℂ) * I) := by
    push_cast; ring
  rw [e, logDeriv_riemannXi_one_sub, norm_neg]
  exact htop (1 - σ) (by linarith) (by linarith)

end RiemannXi
