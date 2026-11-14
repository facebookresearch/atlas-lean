/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.ZeroCounting
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.Analysis.SpecialFunctions.Trigonometric.ComplexNorm
import MathlibExt.NumberTheory.LSeries.ZeroFreeRegion
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# `ζ'/ζ` near the zeros, and good heights

In the strip `-1 ≤ σ ≤ 2` the logarithmic derivative of `ζ` is, up to `O(log |t|)`, the sum of
`1 / (s - ρ)` over the zeros `ρ = β + iγ` with `|t - γ| < 1`. Since such a window contains only
`O(log T)` zeros, every height `T` can be moved by at most `1` to a height `T'` at distance
`≫ 1 / log T'` from all ordinates `γ`, and there `ζ'/ζ(σ + iT') = O(log² T')` uniformly in
`-1 ≤ σ ≤ 2`. To the left of the critical strip, the functional equation gives
`ζ'/ζ(s) = O(log |s|)` away from the trivial zeros.

## Main statements

* `exists_norm_logDeriv_riemannZeta_sub_tsum_le_log`: `ζ'/ζ(s) = ∑_{|t - γ| < 1} 1/(s - ρ)
  + O(log |t|)` for `-1 ≤ σ ≤ 2`.
* `exists_abs_sub_le_one_and_div_log_le_abs_im_sub`: heights at distance `≥ c / log R'` from all
  ordinates of zeros exist in every interval `[R - 1, R + 1]`.
* `exists_good_height_norm_logDeriv_riemannZeta_le`: **good heights**, where
  `‖ζ'/ζ(σ + iT')‖ ≤ C log² T'` for all `-1 ≤ σ ≤ 2`.
* `norm_logDeriv_riemannZeta_conj`: `‖ζ'/ζ(s̄)‖ = ‖ζ'/ζ(s)‖`.
* `neg_logDeriv_riemannZeta_one_sub`: the functional equation for `ζ'/ζ`.
* `exists_norm_logDeriv_riemannZeta_le_log_of_re_le_neg_one`: `‖ζ'/ζ(s)‖ ≤ C log (2‖s‖)` for
  `Re s ≤ -1` at distance `≥ r` from the trivial zeros.
-/

@[expose] public section

universe u

open ArithmeticFunction LSeries RiemannXi ComplexConjugate

/-! ### Conjugation -/

/-- `ζ'(s̄) = conj ζ'(s)`. -/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have hfun : riemannZeta = conj ∘ riemannZeta ∘ conj := by
    funext w; simp [riemannZeta_conj]
  have := congrFun (deriv_conj_conj (f := riemannZeta)) s
  rw [← hfun] at this
  rw [this]; simp

/-- `‖ζ'/ζ(s̄)‖ = ‖ζ'/ζ(s)‖`. -/
theorem norm_logDeriv_riemannZeta_conj (s : ℂ) :
    ‖deriv riemannZeta (conj s) / riemannZeta (conj s)‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ := by
  rw [deriv_riemannZeta_conj, riemannZeta_conj, ← map_div₀, Complex.norm_conj]

/-! ### `ζ'/ζ` as a sum over the nearby zeros -/

/-- The digamma term of the zero-sum expansion is `O(log |t|)` in the strip `-1 ≤ σ ≤ 2`. -/
private lemma norm_digamma_half_add_one_le (C : ℝ)
    (hC : ∀ z : ℂ, z ≠ 0 → -Real.pi + Real.pi / 2 ≤ Complex.arg z →
      Complex.arg z ≤ Real.pi - Real.pi / 2 → ‖Complex.digamma z - Complex.log z‖ ≤ C / ‖z‖)
    {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖Complex.digamma (s / 2 + 1)‖ ≤ 2 * Real.log |s.im| + Real.pi + |C| := by
  set w : ℂ := s / 2 + 1 with hw
  have hwre : w.re = s.re / 2 + 1 := by simp [hw]
  have hwim : w.im = s.im / 2 := by simp [hw]
  have hw0 : w ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hwre] at this; linarith
  have harg : |Complex.arg w| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hwre]; linarith))
  have hCw := hC w hw0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
  have hwn1 : 1 ≤ ‖w‖ := by
    calc (1 : ℝ) ≤ |w.im| := by rw [hwim, abs_div, abs_two]; linarith
      _ ≤ ‖w‖ := Complex.abs_im_le_norm _
  have hwn2 : ‖w‖ ≤ 2 * |s.im| := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im _
      _ = (s.re / 2 + 1) + |s.im| / 2 := by
          rw [hwre, hwim, abs_of_pos (by linarith), abs_div, abs_two]
      _ ≤ 2 * |s.im| := by linarith
  have hlogt : Real.log 2 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) ht
  have hlw : Real.log ‖w‖ ≤ 2 * Real.log |s.im| := by
    calc Real.log ‖w‖ ≤ Real.log (2 * |s.im|) := Real.log_le_log (by linarith) hwn2
      _ = Real.log 2 + Real.log |s.im| := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 2 * Real.log |s.im| := by linarith
  have hlw0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg hwn1
  have hlog : ‖Complex.log w‖ ≤ Real.log ‖w‖ + Real.pi := by
    calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Real.log ‖w‖ + Real.pi := by
          rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlw0]
          linarith [Complex.abs_arg_le_pi w]
  have h3 : ‖Complex.digamma w - Complex.log w‖ ≤ |C| :=
    calc _ ≤ C / ‖w‖ := hCw
      _ ≤ |C| / ‖w‖ := by gcongr; exact le_abs_self C
      _ ≤ |C| := div_le_self (abs_nonneg _) hwn1
  calc ‖Complex.digamma w‖ = ‖(Complex.digamma w - Complex.log w) + Complex.log w‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖Complex.digamma w - Complex.log w‖ + ‖Complex.log w‖ := norm_add_le _ _
    _ ≤ 2 * Real.log |s.im| + Real.pi + |C| := by linarith

/-- The termwise comparison: away from the window, `1/(s - ρ) - 1/(s₁ - ρ)` is
`O(1/(t - γ)²)`; inside it only `-1/(s₁ - ρ)` remains, of size at most `1`. -/
private lemma norm_zero_term_le {s ρ : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2)
    (hβ1 : ρ.re ≤ 1) (hne : ρ.im ≠ s.im) :
    ‖1 / (s - ρ) - 1 / ((2 : ℂ) + (s.im : ℂ) * Complex.I - ρ)
        - (if |s.im - ρ.im| < 1 then 1 / (s - ρ) else 0)‖
      ≤ 6 * (1 / (1 + (s.im - ρ.im) ^ 2)) := by
  set s₁ : ℂ := (2 : ℂ) + (s.im : ℂ) * Complex.I with hs₁
  have h1re : (s₁ - ρ).re = 2 - ρ.re := by simp [hs₁]
  have h1im : (s₁ - ρ).im = s.im - ρ.im := by simp [hs₁]
  have hsim : (s - ρ).im = s.im - ρ.im := by simp
  set x : ℝ := s.im - ρ.im with hx
  have hx0 : x ≠ 0 := fun h => hne (by linarith)
  have hn1 : 1 ≤ ‖s₁ - ρ‖ := by
    calc (1 : ℝ) ≤ |(s₁ - ρ).re| := by rw [h1re, abs_of_pos (by linarith)]; linarith
      _ ≤ _ := Complex.abs_re_le_norm _
  have hpos : 0 < 1 + x ^ 2 := by positivity
  split_ifs with hw
  · have hx2 : x ^ 2 < 1 := by
      have := sq_lt_sq' (abs_lt.mp hw).1 (abs_lt.mp hw).2; simpa using this
    rw [sub_sub_cancel_left, norm_neg, norm_div, norm_one]
    calc 1 / ‖s₁ - ρ‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact hn1
      _ ≤ 6 * (1 / (1 + x ^ 2)) := by
          rw [mul_one_div, le_div_iff₀ hpos]; nlinarith
  · have hx1 : 1 ≤ |x| := not_lt.mp hw
    have hns : |x| ≤ ‖s - ρ‖ := by rw [← hsim]; exact Complex.abs_im_le_norm _
    have hns₁ : |x| ≤ ‖s₁ - ρ‖ := by rw [← h1im]; exact Complex.abs_im_le_norm _
    have hsρ : s - ρ ≠ 0 := fun h => hx0 (by rw [← hsim, h]; simp)
    have hs₁ρ : s₁ - ρ ≠ 0 := fun h => hx0 (by rw [← h1im, h]; simp)
    have hdiff : s₁ - s = ((2 - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hs₁]
    have heq : 1 / (s - ρ) - 1 / (s₁ - ρ) - 0 = (s₁ - s) / ((s - ρ) * (s₁ - ρ)) := by
      field_simp; ring
    rw [heq, norm_div, norm_mul, hdiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
    have hprod : x ^ 2 ≤ ‖s - ρ‖ * ‖s₁ - ρ‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg x]
    rw [div_le_iff₀ (by nlinarith), mul_one_div, div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith

/-- **`ζ'/ζ` near the zeros.** There are constants `C` and `t₀` such that for `-1 ≤ σ ≤ 2` and
`|t| ≥ t₀`, with `t` not the ordinate of a zero,
`‖ζ'(s)/ζ(s) - ∑_{|t - γ| < 1} 1/(s - ρ)‖ ≤ C log |t|`, the sum running over the nontrivial zeros
`ρ = β + iγ` of `ζ` counted with multiplicity (any family `z` listing the zeros of `ξ` with
multiplicity). The sum has finite support. -/
theorem exists_norm_logDeriv_riemannZeta_sub_tsum_le_log :
    ∃ C t₀ : ℝ, ∀ {ι : Type u} (z : ι → ℂ),
      (∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w) →
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → t₀ ≤ |s.im| → (∀ n, (z n).im ≠ s.im) →
        ‖deriv riemannZeta s / riemannZeta s
            - ∑' n, (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0)‖
          ≤ C * Real.log |s.im| := by
  obtain ⟨A, hA⟩ := exists_neg_re_logDeriv_riemannZeta_lt_log_sub_tsum.{u}
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  set K : ℝ := ∑' n, ‖term (fun n => (Λ n : ℂ)) 2 n‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun _ => norm_nonneg _
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K₀ : ℝ := 25 * K + 1 + Real.pi + |Cψ| with hK₀
  refine ⟨K₀ / Real.log 2 + 2 + 24 * |A|, 2, fun {ι} z hz s hσ1 hσ2 ht hord => ?_⟩
  set t : ℝ := s.im with ht_def
  -- the comparison point on `Re = 2`
  set s₁ : ℂ := (2 : ℂ) + (t : ℂ) * Complex.I with hs₁
  have hs₁re : s₁.re = 2 := by simp [hs₁]
  have hs₁im : s₁.im = t := by simp [hs₁]
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hzmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz
  -- `ζ(s) ≠ 0`: a zero would be a zero of `ξ`, hence listed by the family at height `t`
  have hζ : riemannZeta s ≠ 0 := by
    intro hρ
    obtain ⟨n, hn⟩ := exists_eq_of_card_eq_analyticOrderAt hz
      ((riemannXi_eq_zero_iff s).mp (riemannXi_eq_zero_of_riemannZeta_eq_zero ht0 hρ))
    exact hord n (by rw [hn])
  have hs1 : s ≠ 1 := fun h => ht0 (by rw [ht_def, h]; simp)
  have hs₁1 : s₁ ≠ 1 := fun h => ht0 (by rw [← hs₁im, h]; simp)
  have hζ₁ : riemannZeta s₁ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₁re]; norm_num)
  -- the two expansions
  obtain ⟨A₀, B, hAB⟩ := exists_riemannXi_eq_exp_mul_tprod hz
  have hE := neg_logDeriv_riemannZeta_eq hz hAB hs1 hζ
  have hE₁ := neg_logDeriv_riemannZeta_eq hz hAB hs₁1 hζ₁
  rw [logDeriv_apply] at hE hE₁
  have hz0 := ne_zero_of_card_eq_analyticOrderAt hz
  have hz2 := summable_norm_rpow_neg_two hz
  have hma := Complex.summable_one_div_sub_add_one_div hz0 hz2 s
  have hmb := Complex.summable_one_div_sub_add_one_div hz0 hz2 s₁
  -- `ζ'/ζ(s₁)` is bounded
  have hL₁ : ‖deriv riemannZeta s₁ / riemannZeta s₁‖ ≤ K := by
    have hb := norm_logDeriv_riemannZeta_le_tsum (σ := 2) one_lt_two hs₁re.ge
    push_cast at hb
    exact hb
  -- the zero sum at `s₁` is `O(log |t|)`
  have hkey := hA z hz s₁ (by rw [hs₁re]; norm_num) (by rw [hs₁re]) (by rw [hs₁im]; exact ht)
  rw [hs₁im] at hkey
  have hmre : Summable fun n => (1 / (s₁ - z n) + 1 / z n).re := Complex.reCLM.summable hmb
  have hRe₁ : -(deriv riemannZeta s₁ / riemannZeta s₁).re ≥ -K := by
    have := Complex.re_le_norm (deriv riemannZeta s₁ / riemannZeta s₁)
    linarith
  have hSb : ∑' n, (1 / (s₁ - z n) + 1 / z n).re ≤ A * Real.log |t| + K := by linarith
  have hterm : ∀ n, 1 / (1 + (t - (z n).im) ^ 2) ≤ 4 * (1 / (s₁ - z n) + 1 / z n).re :=
    fun n => one_div_one_add_sq_sub_im_le_re (hzmem n).2.1 (hzmem n).2.2 t
  set g : ι → ℝ := fun n => 6 * (1 / (1 + (t - (z n).im) ^ 2)) with hg
  have hg_le : ∀ n, g n ≤ 24 * (1 / (s₁ - z n) + 1 / z n).re := by
    intro n; simp only [hg]; linarith [hterm n]
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; positivity
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hg_le (hmre.mul_left 24)
  have hgt : ∑' n, g n ≤ 24 * (A * Real.log |t| + K) := by
    calc ∑' n, g n ≤ ∑' n, 24 * (1 / (s₁ - z n) + 1 / z n).re :=
          hgs.tsum_le_tsum hg_le (hmre.mul_left 24)
      _ = 24 * ∑' n, (1 / (s₁ - z n) + 1 / z n).re := tsum_mul_left
      _ ≤ 24 * (A * Real.log |t| + K) := by linarith
  -- the remainder after removing the window
  set near : ι → ℂ := fun n => if |t - (z n).im| < 1 then 1 / (s - z n) else 0 with hnear
  set r : ι → ℂ := fun n => (1 / (s - z n) + 1 / z n) - (1 / (s₁ - z n) + 1 / z n) - near n
    with hr
  have hr_le : ∀ n, ‖r n‖ ≤ g n := by
    intro n
    have h := norm_zero_term_le (ρ := z n) hσ1 hσ2 (hzmem n).2.2 (hord n)
    have : r n = 1 / (s - z n) - 1 / ((2 : ℂ) + (s.im : ℂ) * Complex.I - z n)
        - (if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0) := by
      simp only [hr, hnear, hs₁, ht_def]; ring
    rw [this]; exact h
  have hrs : Summable r := Summable.of_norm_bounded hgs hr_le
  have hab : Summable fun n => (1 / (s - z n) + 1 / z n) - (1 / (s₁ - z n) + 1 / z n) :=
    hma.sub hmb
  have hnears : Summable near := by
    have : near = fun n => ((1 / (s - z n) + 1 / z n) - (1 / (s₁ - z n) + 1 / z n)) - r n := by
      funext n; simp only [hr]; ring
    rw [this]; exact hab.sub hrs
  have hrt : ‖∑' n, r n‖ ≤ ∑' n, g n :=
    (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hr_le hgs)).trans
      (Summable.tsum_le_tsum hr_le (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hr_le hgs)
        hgs)
  have hsplit : ∑' n, r n =
      (∑' n, (1 / (s - z n) + 1 / z n)) - (∑' n, (1 / (s₁ - z n) + 1 / z n)) - ∑' n, near n := by
    rw [← hma.tsum_sub hmb, ← hab.tsum_sub hnears]
  -- the identity
  have hid : deriv riemannZeta s / riemannZeta s - ∑' n, near n
      = deriv riemannZeta s₁ / riemannZeta s₁ - (1 / (s - 1) - 1 / (s₁ - 1))
        - (Complex.digamma (s / 2 + 1) - Complex.digamma (s₁ / 2 + 1)) / 2 + ∑' n, r n := by
    rw [hsplit]; linear_combination -hE + hE₁
  have hψ := norm_digamma_half_add_one_le Cψ hCψ hσ1 hσ2 ht
  have hψ₁ := norm_digamma_half_add_one_le Cψ hCψ (s := s₁) (by rw [hs₁re]; norm_num)
    (by rw [hs₁re]) (by rw [hs₁im]; exact ht)
  rw [hs₁im] at hψ₁
  have hinv : ∀ u : ℂ, u.im = t → ‖1 / (u - 1)‖ ≤ 1 / 2 := by
    intro u hu
    have hn : 2 ≤ ‖u - 1‖ := by
      calc (2 : ℝ) ≤ |t| := ht
        _ = |(u - 1).im| := by simp [hu]
        _ ≤ ‖u - 1‖ := Complex.abs_im_le_norm _
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hn
  have hi := hinv s rfl
  have hi₁ := hinv s₁ hs₁im
  have hbound : ‖deriv riemannZeta s / riemannZeta s - ∑' n, near n‖
      ≤ K + (1 / 2 + 1 / 2) +
        (‖Complex.digamma (s / 2 + 1)‖ + ‖Complex.digamma (s₁ / 2 + 1)‖) / 2 + ∑' n, g n := by
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ hrt)
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sub_le _ _).trans (add_le_add hL₁ ?_)
      exact (norm_sub_le _ _).trans (add_le_add hi hi₁)
    · rw [norm_div, Complex.norm_ofNat]
      gcongr
      exact norm_sub_le _ _
  have hlogt : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hAl : A * Real.log |t| ≤ |A| * Real.log |t| :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  have hKl : K₀ ≤ K₀ / Real.log 2 * Real.log |t| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    have : 0 ≤ K₀ := by rw [hK₀]; positivity
    nlinarith
  have hexp : (K₀ / Real.log 2 + 2 + 24 * |A|) * Real.log |t|
      = K₀ / Real.log 2 * Real.log |t| + 2 * Real.log |t| + 24 * (|A| * Real.log |t|) := by ring
  change ‖deriv riemannZeta s / riemannZeta s - ∑' n, near n‖ ≤ _
  rw [hexp]
  have : 0 ≤ |Cψ| := abs_nonneg _
  linarith

/-! ### Heights away from the ordinates of the zeros -/

/-- **Heights away from the ordinates of the zeros.** There are constants `c > 0` and `R₀` such
that every `R ≥ R₀` can be moved by at most `1` to some `R'` whose distance from the ordinate of
every nontrivial zero of `ζ` is at least `c / log R'`. -/
theorem exists_abs_sub_le_one_and_div_log_le_abs_im_sub :
    ∃ c > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∃ R' : ℝ, |R' - R| ≤ 1 ∧
      ∀ ρ ∈ riemannZetaNontrivialZeros, c / Real.log R' ≤ |ρ.im - R'| := by
  obtain ⟨C, hC⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{0}
  set N : ℂ → ℕ := fun w => (analyticOrderAt riemannXi w).toNat with hN
  let z : (Σ w : ℂ, Fin (N w)) → ℂ := Sigma.fst
  have hz : ∀ w, ENat.card {n // z n = w} = analyticOrderAt riemannXi w :=
    Complex.card_sigma_fin_analyticOrderAt differentiable_riemannXi riemannXi_zero_ne_zero
  have hN1 : ∀ ρ ∈ riemannZetaNontrivialZeros, 1 ≤ N ρ := by
    intro ρ hρ
    have hne : analyticOrderAt riemannXi ρ ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨differentiable_riemannXi.analyticAt ρ, (riemannXi_eq_zero_iff ρ).mpr hρ⟩
    simp only [hN]
    rcases ENat.ne_top_iff_exists.mp (analyticOrderAt_riemannXi_ne_top ρ) with ⟨n, hn⟩
    rw [← hn] at hne ⊢
    simp only [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  have hfin := fun R : ℝ => finite_setOf_mem_riemannZetaNontrivialZeros_abs_im_sub_le R 2
  -- the count of zeros near height `R`
  have hcount : ∀ R : ℝ, 2 ≤ R → ((hfin R).toFinset.card : ℝ) ≤ 5 * C * Real.log R := by
    intro R hR
    set S := (hfin R).toFinset with hS
    obtain ⟨hs, ht⟩ := hC z hz R hR
    have key := (hs.sum_le_tsum (S.sigma fun w => (Finset.univ : Finset (Fin (N w))))
      (fun n _ => by positivity)).trans ht
    rw [Finset.sum_sigma] at key
    simp only [z, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at key
    have hterm : ∀ ρ ∈ S, (1 : ℝ) ≤ 5 * ((N ρ : ℝ) * (1 / (1 + (R - ρ.im) ^ 2))) := by
      intro ρ hρ
      rw [hS, Set.Finite.mem_toFinset] at hρ
      obtain ⟨hρ, h2⟩ := hρ
      have h1 : (1 : ℝ) ≤ N ρ := by exact_mod_cast hN1 ρ hρ
      have hsq : (R - ρ.im) ^ 2 ≤ 4 := by
        have : |R - ρ.im| ≤ 2 := by rw [abs_sub_comm]; exact h2
        rw [abs_le] at this
        nlinarith
      have hf : 1 / 5 ≤ 1 / (1 + (R - ρ.im) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      nlinarith
    have := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at this
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    linarith
  set B : ℝ := |5 * C| with hB
  have hB0 : 0 ≤ B := abs_nonneg _
  refine ⟨1 / (2 * (B + 1)), by positivity, Real.exp 2, ?_⟩
  intro R hR
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hR3 : 3 ≤ R := le_trans he2 hR
  have hlogR : 2 ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hR
  set S := (hfin R).toFinset with hS
  set G : Finset ℝ := S.image Complex.im with hG
  have hGcard : (G.card : ℝ) ≤ B * Real.log R := by
    have h1 : (G.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
    have h2 := hcount R (by linarith)
    have h3 : 5 * C * Real.log R ≤ B * Real.log R :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  set m : ℕ := ⌈B * Real.log R⌉₊ with hm
  have hmG : G.card ≤ m := by
    have : (G.card : ℝ) ≤ m := hGcard.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hm1 : ((m : ℝ) + 1) ≤ (B + 1) * Real.log R := by
    have := Nat.ceil_lt_add_one (show 0 ≤ B * Real.log R by positivity)
    rw [← hm] at this
    nlinarith
  have hmpos : (0 : ℝ) < m + 1 := by positivity
  set δ : ℝ := 2 / ((m : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by positivity
  let t : ℕ → ℝ := fun j => R - 1 + j * δ
  -- some candidate is far from every ordinate in `G`
  have hgood : ∃ j ∈ Finset.range (m + 1), ∀ γ ∈ G, δ / 2 ≤ |γ - t j| := by
    by_contra hcon
    push Not at hcon
    choose! g hgG hgd using hcon
    have hinj : Set.InjOn g (Finset.range (m + 1) : Set ℕ) := by
      intro j hj k hk hjk
      by_contra hne
      have h1 := hgd j hj
      have h2 := hgd k hk
      rw [hjk] at h1
      have h3 : |t j - t k| < δ := by
        have := abs_sub_le (t j) (g k) (t k)
        rw [abs_sub_comm (t j) (g k)] at this
        linarith
      have h4 : δ ≤ |t j - t k| := by
        have hjk' : (1 : ℝ) ≤ |(j : ℝ) - k| := by
          rcases lt_or_gt_of_ne hne with h | h
          · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_pos (by linarith)]
            linarith
          · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
            rw [abs_of_pos (by linarith)]
            linarith
        have : t j - t k = ((j : ℝ) - k) * δ := by simp only [t]; ring
        rw [this, abs_mul, abs_of_pos hδpos]
        nlinarith
      linarith
    have := Finset.card_le_card_of_injOn g (fun j hj => hgG j hj) hinj
    simp only [Finset.card_range] at this
    omega
  obtain ⟨j, hj, hjG⟩ := hgood
  have hjm : (j : ℝ) ≤ m := by
    have := Finset.mem_range.mp hj
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjδ : (j : ℝ) * δ ≤ 2 := by
    have : (j : ℝ) * δ = 2 * (j / ((m : ℝ) + 1)) := by simp only [hδ]; ring
    rw [this]
    have : (j : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hmpos]; linarith
    linarith
  have hjδ0 : 0 ≤ (j : ℝ) * δ := by positivity
  refine ⟨t j, ?_, ?_⟩
  · simp only [t]
    rw [abs_le]; constructor <;> linarith
  -- lower bound for `log (t j)`
  have htj : R / 2 ≤ t j := by simp only [t]; linarith
  have hlogt : Real.log R / 2 ≤ Real.log (t j) := by
    have h1 : Real.log (R / 2) ≤ Real.log (t j) :=
      Real.log_le_log (by linarith) htj
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    linarith
  have hlt0 : 0 < Real.log (t j) := by linarith
  have hc_le : 1 / (2 * (B + 1)) / Real.log (t j) ≤ δ / 2 := by
    have : δ / 2 = 1 / ((m : ℝ) + 1) := by simp only [hδ]; ring
    rw [this, div_le_div_iff₀ hlt0 hmpos]
    have hB1 : 0 < B + 1 := by linarith
    have h1 : 1 / (2 * (B + 1)) * ((m : ℝ) + 1) ≤
        1 / (2 * (B + 1)) * ((B + 1) * Real.log R) :=
      mul_le_mul_of_nonneg_left hm1 (by positivity)
    have h2 : 1 / (2 * (B + 1)) * ((B + 1) * Real.log R) = Real.log R / 2 := by
      field_simp
    linarith
  intro ρ hρ
  by_cases hnear : |ρ.im - R| ≤ 2
  · have hmem : ρ.im ∈ G := by
      rw [hG, Finset.mem_image]
      exact ⟨ρ, by rw [hS, Set.Finite.mem_toFinset]; exact ⟨hρ, hnear⟩, rfl⟩
    exact hc_le.trans (hjG _ hmem)
  · push Not at hnear
    have hfar : 1 ≤ |ρ.im - t j| := by
      have h1 := abs_sub_abs_le_abs_sub (ρ.im - R) (t j - R)
      have h2 : |t j - R| ≤ 1 := by
        simp only [t]; rw [abs_le]; constructor <;> linarith
      have h3 : ρ.im - R - (t j - R) = ρ.im - t j := by ring
      rw [h3] at h1
      linarith
    have : 1 / (2 * (B + 1)) / Real.log (t j) ≤ 1 := by
      rw [div_le_one hlt0]
      have : 1 / (2 * (B + 1)) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      linarith
    linarith

/-- **Good heights.** There are constants `C` and `T₀` such that every `T ≥ T₀` can be moved by
at most `1` to a height `T'` that is not the ordinate of any nontrivial zero of `ζ` and on which
`‖ζ'/ζ(σ + iT')‖ ≤ C log² T'` for all `-1 ≤ σ ≤ 2`. -/
theorem exists_good_height_norm_logDeriv_riemannZeta_le :
    ∃ C T₀ : ℝ, ∀ T ≥ T₀, ∃ T' : ℝ, |T' - T| ≤ 1 ∧
      (∀ ρ ∈ riemannZetaNontrivialZeros, ρ.im ≠ T') ∧
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖deriv riemannZeta (σ + T' * Complex.I) / riemannZeta (σ + T' * Complex.I)‖ ≤
          C * Real.log T' ^ 2 := by
  obtain ⟨c, hc, R₀, hR⟩ := exists_abs_sub_le_one_and_div_log_le_abs_im_sub
  obtain ⟨C₁, t₀, h76⟩ := exists_norm_logDeriv_riemannZeta_sub_tsum_le_log.{0}
  obtain ⟨C₄, h74⟩ := exists_tsum_one_div_one_add_sq_sub_im_le_log.{0}
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  have hzmem := mem_riemannZetaNontrivialZeros_of_card_eq_analyticOrderAt hz
  refine ⟨2 * |C₄| / c + |C₁|, max R₀ (max (t₀ + 1) (Real.exp 1 + 1)), ?_⟩
  intro T hT
  obtain ⟨T', hT'1, hT'far⟩ := hR T (le_trans (le_max_left _ _) hT)
  have hTt : t₀ + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTe : Real.exp 1 + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT'lo : T - 1 ≤ T' := by rw [abs_le] at hT'1; linarith
  have hT'e : Real.exp 1 ≤ T' := by linarith
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hT'2 : (2 : ℝ) ≤ T' := le_trans he2 hT'e
  have hlog1 : 1 ≤ Real.log T' := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hT'e
  have hlpos : 0 < Real.log T' := by linarith
  have hcl : 0 < c / Real.log T' := div_pos hc hlpos
  have hord : ∀ ρ ∈ riemannZetaNontrivialZeros, ρ.im ≠ T' := by
    intro ρ hρ heq
    have := hT'far ρ hρ
    rw [heq, sub_self, abs_zero] at this
    linarith
  refine ⟨T', hT'1, hord, fun σ hσ1 hσ2 => ?_⟩
  set s : ℂ := σ + T' * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = T' := by simp [hs]
  have habs : |s.im| = T' := by rw [hsim, abs_of_pos (by linarith)]
  have key := h76 z hz s (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2)
    (by rw [habs]; linarith) (fun n => by rw [hsim]; exact hord _ (hzmem n))
  rw [habs] at key
  set f : ι → ℂ := fun n => if |s.im - (z n).im| < 1 then 1 / (s - z n) else 0 with hf
  set F : Finset ι := (finite_setOf_abs_im_le_of_card_eq_analyticOrderAt hz (T' + 1)).toFinset
    with hF
  have hzero : ∀ n ∉ F, f n = 0 := by
    intro n hn
    simp only [hf]
    rw [ite_eq_right]
    intro hlt
    apply hn
    rw [hF, Set.Finite.mem_toFinset]
    change |(z n).im| ≤ T' + 1
    rw [hsim] at hlt
    have := abs_sub_abs_le_abs_sub (z n).im T'
    rw [abs_sub_comm (z n).im T', abs_of_pos (by linarith : (0 : ℝ) < T')] at this
    linarith
  have htsum : ∑' n, f n = ∑ n ∈ F, f n := tsum_eq_sum hzero
  have hterm : ∀ n ∈ F, ‖f n‖ ≤
      2 * (Real.log T' / c) * (1 / (1 + (T' - (z n).im) ^ 2)) := by
    intro n _
    simp only [hf]
    split_ifs with hlt
    · rw [hsim] at hlt
      have hfar := hT'far _ (hzmem n)
      rw [abs_sub_comm] at hfar
      have hpos : 0 < |T' - (z n).im| := lt_of_lt_of_le hcl hfar
      have hn1 : |T' - (z n).im| ≤ ‖s - z n‖ := by
        have := Complex.abs_im_le_norm (s - z n)
        simpa [Complex.sub_im, hsim] using this
      have hb1 : ‖1 / (s - z n)‖ ≤ Real.log T' / c := by
        rw [norm_div, norm_one, div_le_div_iff₀ (lt_of_lt_of_le hpos hn1) hc]
        have : c ≤ Real.log T' * |T' - (z n).im| := by
          rw [div_le_iff₀ hlpos] at hfar; linarith
        nlinarith
      have hsq : (T' - (z n).im) ^ 2 ≤ 1 := by
        rw [abs_lt] at hlt; nlinarith
      have hb2 : 1 / 2 ≤ 1 / (1 + (T' - (z n).im) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity); linarith
      have : 0 ≤ Real.log T' / c := by positivity
      nlinarith
    · rw [norm_zero]; positivity
  have hsumle : ‖∑' n, f n‖ ≤ 2 * (Real.log T' / c) * (C₄ * Real.log T') := by
    rw [htsum]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    obtain ⟨hs4, ht4⟩ := h74 z hz T' hT'2
    exact mul_le_mul_of_nonneg_left ((hs4.sum_le_tsum F fun n _ => by positivity).trans ht4)
      (by positivity)
  have htri : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      ‖deriv riemannZeta s / riemannZeta s - ∑' n, f n‖ + ‖∑' n, f n‖ := by
    simpa using norm_add_le (deriv riemannZeta s / riemannZeta s - ∑' n, f n) (∑' n, f n)
  have h1 : C₁ * Real.log T' ≤ |C₁| * Real.log T' ^ 2 := by
    have : C₁ * Real.log T' ≤ |C₁| * Real.log T' :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlpos.le
    have h2 : |C₁| * Real.log T' ≤ |C₁| * Real.log T' ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
    linarith
  have h2 : 2 * (Real.log T' / c) * (C₄ * Real.log T') ≤ 2 * |C₄| / c * Real.log T' ^ 2 := by
    have : 2 * (Real.log T' / c) * (C₄ * Real.log T') = 2 * C₄ / c * Real.log T' ^ 2 := by
      field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply div_le_div_of_nonneg_right _ hc.le
    linarith [le_abs_self C₄]
  nlinarith

/-! ### `ζ'/ζ` to the left of the critical strip -/

/-- `‖ψ(v)‖ ≤ log ‖v‖ + C` for `Re v > 0` and `‖v‖ ≥ 1`, where `ψ = Γ'/Γ`. -/
theorem Complex.exists_norm_digamma_le_log_add :
    ∃ C : ℝ, ∀ v : ℂ, 0 < v.re → 1 ≤ ‖v‖ → ‖digamma v‖ ≤ Real.log ‖v‖ + C := by
  obtain ⟨C, hC⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  refine ⟨Real.pi + |C|, fun v hv hv1 => ?_⟩
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have harg : |arg v| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hCv := hC v hv0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
  have h1 : C / ‖v‖ ≤ |C| :=
    (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)).trans
      (div_le_self (abs_nonneg _) hv1)
  have h2 : ‖log v‖ ≤ Real.log ‖v‖ + Real.pi := by
    calc ‖log v‖ ≤ |(log v).re| + |(log v).im| := norm_le_abs_re_add_abs_im _
      _ ≤ Real.log ‖v‖ + Real.pi := by
          rw [log_re, log_im, abs_of_nonneg (Real.log_nonneg hv1)]
          gcongr
          exact abs_arg_le_pi v
  calc ‖digamma v‖ = ‖(digamma v - log v) + log v‖ := by ring_nf
    _ ≤ ‖digamma v - log v‖ + ‖log v‖ := norm_add_le _ _
    _ ≤ Real.log ‖v‖ + (Real.pi + |C|) := by linarith

/-- **The functional equation for `ζ'/ζ`**: for `Re w > 1` with `cos (πw/2) ≠ 0`,
`-ζ'/ζ(1 - w) = -log 2π + ψ(w) - (π/2) tan (πw/2) + ζ'/ζ(w)`. -/
theorem neg_logDeriv_riemannZeta_one_sub {w : ℂ} (hw : 1 < w.re)
    (hc : Complex.cos (Real.pi * w / 2) ≠ 0) :
    -logDeriv riemannZeta (1 - w) = -Complex.log (2 * Real.pi) + Complex.digamma w
      - (Real.pi / 2) * (Complex.sin (Real.pi * w / 2) / Complex.cos (Real.pi * w / 2))
      + logDeriv riemannZeta w := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
  have hwn : ∀ n : ℕ, w ≠ -n := fun n h => by
    rw [h] at hw; simp at hw; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')
  have hev : (fun v => riemannZeta (1 - v)) =ᶠ[nhds w]
      (fun v => ((2 * (2 * (Real.pi : ℂ)) ^ (-v) * Complex.Gamma v) *
        Complex.cos (Real.pi * v / 2)) * riemannZeta v) := by
    have ho : IsOpen {v : ℂ | 1 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hw] with v hv
    have hv1 : v ≠ 1 := fun h => by rw [h] at hv; simp at hv
    have hvn : ∀ n : ℕ, v ≠ -n := fun n h => by
      rw [h] at hv; simp at hv; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [riemannZeta_one_sub hvn hv1]
  have hcomp : logDeriv (fun v => riemannZeta (1 - v)) w = -logDeriv riemannZeta (1 - w) := by
    have hg : HasDerivAt (fun v : ℂ => 1 - v) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub 1
    rw [show (fun v => riemannZeta (1 - v)) = riemannZeta ∘ (fun v : ℂ => 1 - v) from rfl,
      logDeriv_comp (differentiableAt_riemannZeta (by intro h; apply hw0; linear_combination -h))
        hg.differentiableAt, hg.deriv]
    ring
  have hAd : HasDerivAt (fun v : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-v))
      (2 * ((2 * (Real.pi : ℂ)) ^ (-w) * Complex.log (2 * Real.pi) * (-1))) w :=
    ((hasDerivAt_id w).neg.const_cpow (Or.inl h2pi)).const_mul 2
  have hcd : HasDerivAt (fun v : ℂ => Complex.cos (Real.pi * v / 2))
      (-Complex.sin (Real.pi * w / 2) * (Real.pi / 2)) w := by
    have := ((hasDerivAt_id w).const_mul (Real.pi : ℂ)).div_const 2
    exact ((Complex.hasDerivAt_cos _).comp w this).congr_deriv (by simp)
  have hA0 : 2 * (2 * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by simp [h2pi]
  have hG0 : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw.le
  have hGd : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma _ hwn
  have hZd : DifferentiableAt ℂ riemannZeta w :=
    differentiableAt_riemannZeta (fun h => by rw [h] at hw; simp at hw)
  rw [← hcomp, logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds,
    ← logDeriv_apply, logDeriv_fun_mul (f := fun v => (2 * (2 * (Real.pi : ℂ)) ^ (-v) *
        Complex.Gamma v) * Complex.cos (Real.pi * v / 2)) w
      (mul_ne_zero (mul_ne_zero hA0 hG0) hc) hZ0
      ((hAd.differentiableAt.mul hGd).mul hcd.differentiableAt) hZd,
    logDeriv_fun_mul (f := fun v => (2 * (2 * (Real.pi : ℂ)) ^ (-v) * Complex.Gamma v)) w
      (mul_ne_zero hA0 hG0) hc (hAd.differentiableAt.mul hGd) hcd.differentiableAt,
    logDeriv_fun_mul (f := fun v : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-v)) w hA0 hG0
      hAd.differentiableAt hGd]
  rw [logDeriv_apply (fun v : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-v)), hAd.deriv,
    logDeriv_apply (fun v : ℂ => Complex.cos (Real.pi * v / 2)), hcd.deriv,
    ← Complex.digamma_def, logDeriv_apply riemannZeta w]
  field_simp
  ring

/-- **`ζ'/ζ` to the left of the critical strip.** For every `r > 0` there is a constant `C` such
that `‖ζ'(s)/ζ(s)‖ ≤ C log (2‖s‖)` for every `s` with `Re s ≤ -1` at distance at least `r` from
each trivial zero `-2, -4, …`. -/
theorem exists_norm_logDeriv_riemannZeta_le_log_of_re_le_neg_one {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ≤ -1 → (∀ m : ℕ, 0 < m → r ≤ ‖s + 2 * (m : ℂ)‖) →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (2 * ‖s‖) := by
  obtain ⟨Kζ, -, hKζ⟩ := exists_norm_logDeriv_riemannZeta_le (δ := 1) one_pos
  obtain ⟨Cψ, hCψ⟩ := Complex.exists_norm_digamma_le_log_add
  set ρ : ℝ := min r 1 with hρ
  have hρ0 : 0 < ρ := lt_min hr one_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := ‖Complex.log (2 * Real.pi)‖ + |Cψ| + Real.pi / 2 * (1 / ρ + 1) + |Kζ| with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A / Real.log 2 + 1, fun s hs hdist => ?_⟩
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 1 - s.re := by simp [hw]
  have hw2 : 2 ≤ w.re := by linarith
  have hs1 : 1 ≤ ‖s‖ := by
    have h1 := Complex.abs_re_le_norm s
    have h2 : |s.re| = -s.re := abs_of_nonpos (by linarith)
    linarith
  have hk : ∀ k : ℤ, ρ ≤ ‖s - 2 * (k : ℂ)‖ := by
    intro k
    rcases le_or_gt 0 k with hk0 | hk0
    · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      have hre : (s - 2 * (k : ℂ)).re = s.re - 2 * k := by simp
      calc ρ ≤ 1 := min_le_right _ _
        _ ≤ |(s - 2 * (k : ℂ)).re| := by
            rw [hre, abs_of_nonpos (by linarith)]; linarith
        _ ≤ _ := Complex.abs_re_le_norm _
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨k.natAbs, by omega⟩
      have hm0 : 0 < m := by omega
      calc ρ ≤ r := min_le_left _ _
        _ ≤ ‖s + 2 * (m : ℂ)‖ := hdist m hm0
        _ = _ := by rw [hm]; push_cast; ring_nf
  obtain ⟨hsin0, hcot⟩ := Complex.norm_cos_div_sin_pi_mul_div_two_le hρ0 s hk
  have hcos_w : Complex.cos (Real.pi * w / 2) = Complex.sin (Real.pi * s / 2) := by
    rw [show (Real.pi : ℂ) * w / 2 = Real.pi / 2 - Real.pi * s / 2 by rw [hw]; ring,
      Complex.cos_pi_div_two_sub]
  have hsin_w : Complex.sin (Real.pi * w / 2) = Complex.cos (Real.pi * s / 2) := by
    rw [show (Real.pi : ℂ) * w / 2 = Real.pi / 2 - Real.pi * s / 2 by rw [hw]; ring,
      Complex.sin_pi_div_two_sub]
  have hid := neg_logDeriv_riemannZeta_one_sub (w := w) (by linarith)
    (by rw [hcos_w]; exact hsin0)
  have h1w : 1 - w = s := by rw [hw]; ring
  rw [h1w, hcos_w, hsin_w] at hid
  have hL : deriv riemannZeta s / riemannZeta s = Complex.log (2 * Real.pi) - Complex.digamma w
      + (Real.pi / 2) * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2))
      - deriv riemannZeta w / riemannZeta w := by
    rw [← logDeriv_apply, ← logDeriv_apply]; linear_combination -hid
  have hwn1 : 1 ≤ ‖w‖ := le_trans (by linarith) (Complex.re_le_norm w)
  have hψ := hCψ w (by linarith) hwn1
  have hwle : ‖w‖ ≤ 2 * ‖s‖ := by
    calc ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ ≤ 2 * ‖s‖ := by simp; linarith
  have hlogw : Real.log ‖w‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by linarith) hwle
  have hlog2 : Real.log 2 ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by norm_num) (by linarith)
  have hKw := hKζ w (by linarith)
  have hpiterm : ‖(Real.pi / 2 : ℂ) * (Complex.cos (Real.pi * s / 2) /
      Complex.sin (Real.pi * s / 2))‖ ≤ Real.pi / 2 * (1 / ρ + 1) := by
    rw [norm_mul]
    have : ‖(Real.pi / 2 : ℂ)‖ = Real.pi / 2 := by
      rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this]; gcongr
  have hmain : ‖deriv riemannZeta s / riemannZeta s‖ ≤ Real.log (2 * ‖s‖) + A := by
    rw [hL]
    have e1 := norm_sub_le (Complex.log (2 * Real.pi) - Complex.digamma w
      + (Real.pi / 2) * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)))
      (deriv riemannZeta w / riemannZeta w)
    have e2 := norm_add_le (Complex.log (2 * Real.pi) - Complex.digamma w)
      ((Real.pi / 2) * (Complex.cos (Real.pi * s / 2) / Complex.sin (Real.pi * s / 2)))
    have e3 := norm_sub_le (Complex.log (2 * Real.pi)) (Complex.digamma w)
    have e4 := le_abs_self Kζ
    have e5 := le_abs_self Cψ
    rw [hA]; linarith
  have hAl : A ≤ A / Real.log 2 * Real.log (2 * ‖s‖) := by
    calc A = A / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ _ := by gcongr
  nlinarith
