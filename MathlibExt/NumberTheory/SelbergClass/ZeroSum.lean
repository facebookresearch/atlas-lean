/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.Analysis.Complex.PhragmenLindelofStrip
import MathlibExt.Analysis.SpecialFunctions.Gamma.Vertical
import MathlibExt.Analysis.SpecialFunctions.Gamma.DigammaAsymptotics
import MathlibExt.Analysis.Complex.RectangleResidue
import MathlibExt.Analysis.Complex.HadamardFactorization
import MathlibExt.NumberTheory.LSeries.VerticalLine
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Landau's formula for the Selberg class

For `a` in the Selberg class with continuation `F` and `-F'/F = ∑ Λ(n) n^{-s}` on `Re s > 1`,
the sum of `n^ρ` over the zeros `ρ = β + iγ` of `F` with `β ≥ 0` and `|γ| ≤ T` is
`-(T/π) Λ(n) + O(n^{3/2} log² T)`, uniformly in `n > 1` and `T ≥ 2`.

The proof integrates `H'/H(s) n^s` around the rectangle `[-1/2, 3/2] × [-T', T']`, where `H` is
the entire completed function `s^m Q^s ∏ Γ(α_i s + r_i) (s - 1)^m F(s)` and `T'` is a good
height near `T`. The right side contributes `T Λ(n)/π` up to `O(n^{3/2})` (the Dirichlet series
and Gamma factors against `n^{it}`), the left side is reflected to the right by the functional
equation, and the horizontal sides are `O(n^{3/2} log² T)` by Landau's lemma: for an entire
function of polynomial growth, `H'/H` is the sum of `1/(s - ρ)` over nearby zeros plus `O(log T)`.

## Main statements

* `SelbergClass.exists_norm_finsum_zeros_cpow_add_le`: Landau's formula.
-/

open ArithmeticFunction

@[expose] public section

namespace SelbergClass

/-- `x ^ s = exp (log x * s)` for real `x > 0`. -/
private lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne' : (x : ℂ) ≠ 0),
    Complex.ofReal_log hx.le]

/-- The residue theorem on a rectangle with corners `z`, `w`, written with the four sides. -/
private lemma integral_boundary_rect_add_sum_div_sub {z w : ℂ} (S : Finset ℂ) (r f g : ℂ → ℂ)
    (hin : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)
    (hg : DifferentiableOn ℂ g (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (hf : ∀ s ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, s ∉ S →
      f s = g s + ∑ p ∈ S, r p / (s - p)) :
    (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * Complex.I))
        - (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (w.im : ℂ) * Complex.I))
      + Complex.I • (∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I • (∫ y : ℝ in z.im..w.im, f ((z.re : ℂ) + (y : ℂ) * Complex.I))
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ p ∈ S, r p :=
  RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum ⟨z, w⟩ S r f g hin hg hf

/-! ### Setup: the completed function and growth in vertical strips -/

/-- A Selberg function is bounded on `Re s ≥ 2`. -/
private lemma norm_le_of_two_le_re (a : ArithmeticFunction ℂ) (F : ℂ → ℂ) (hF :
    IsLSeriesContinuation a F)
    (Ca : ℝ) (hCa : ∀ n : ℕ, ‖a n‖ ≤ Ca * (n : ℝ) ^ (1 / 2 : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, 2 ≤ s.re → ‖F s‖ ≤ B := by
  have hsum2 : LSeriesSummable (fun n => a n) 2 :=
    LSeriesSummable_of_le_const_mul_rpow (x := 3/2) (by norm_num) ⟨Ca, fun n _ => by
      convert hCa n using 3; norm_num⟩
  have hsumn : Summable fun n => ‖LSeries.term (fun n => a n) 2 n‖ := summable_norm_iff.2 hsum2
  refine ⟨∑' n, ‖LSeries.term (fun n => a n) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _),
    fun s hs => ?_⟩
  rw [hF.1 s (by linarith), LSeries]
  exact tsum_of_norm_bounded hsumn.hasSum fun n =>
    LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n

/-- A Selberg function is bounded below on `Re s = 2`. -/
private lemma exists_le_norm_of_re_eq_two (a : ArithmeticFunction ℂ) (F : ℂ → ℂ) (hF :
    IsLSeriesContinuation a F)
    (b : ℕ → ℂ) (hlog : IsEulerLog a b) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, s.re = 2 → κ ≤ ‖F s‖ := by
  have hb2 : LSeriesSummable b 2 := (hlog.2 2 (by norm_num)).1
  have hbn : Summable fun n => ‖LSeries.term b 2 n‖ := summable_norm_iff.2 hb2
  set K := ∑' n, ‖LSeries.term b 2 n‖ with hK
  refine ⟨Real.exp (-K), Real.exp_pos _, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  rw [hF.1 s hs1, (hlog.2 s hs1).2, Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h1 : ‖LSeries b s‖ ≤ K := by
    rw [LSeries]
    exact tsum_of_norm_bounded hbn.hasSum fun n =>
      LSeries.norm_term_le_of_re_le_re _ (by simp [hs]) n
  have h2 := Complex.abs_re_le_norm (LSeries b s)
  have h3 := neg_abs_le (LSeries b s).re
  linarith

/-- Stirling for one gamma factor between the lines `Re s = 4` and `Re s = -3`. -/
private lemma norm_Gamma_line_four_mul_inv_line_neg_three_le (α : ℝ) (hα : 0 < α) (r : ℂ) :
    ∃ M T : ℝ, 0 ≤ M ∧ ∀ t : ℝ, T ≤ |t| →
      ‖Complex.Gamma (α * (4 + t * Complex.I) + r)‖ *
        ‖(Complex.Gamma (α * (-3 + t * Complex.I) + r))⁻¹‖ ≤ M * |t| ^ (7 * α) := by
  obtain ⟨R, hR1, hR⟩ := Complex.exists_norm_Gamma_vertical_le_mul_rpow (4 * α + r.re) (-3 * α +
      r.re)
  have hK : 0 < α + |r.im| := by positivity
  refine ⟨3 * (α + |r.im|) ^ (7 * α), max 1 ((R + |r.im|) / α),
    by positivity, fun t ht => ?_⟩
  have hb : (α : ℂ) * (4 + t * Complex.I) + r =
      ((4 * α + r.re : ℝ) : ℂ) + ((α * t + r.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  have hc : (α : ℂ) * (-3 + t * Complex.I) + r =
      ((-3 * α + r.re : ℝ) : ℂ) + ((α * t + r.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp; ring
  rw [hb, hc]
  have htR : (R + |r.im|) / α ≤ |t| := le_trans (le_max_right _ _) ht
  rw [div_le_iff₀ hα] at htR
  have hat : |α * t| = α * |t| := by rw [abs_mul, abs_of_pos hα]
  have hu_ge : R ≤ |α * t + r.im| := by
    have := abs_add_le (α * t + r.im) (-r.im)
    rw [abs_neg, add_neg_cancel_right, hat] at this
    linarith
  have hu_le : |α * t + r.im| ≤ (α + |r.im|) * |t| := by
    have ht1 : 1 ≤ |t| := le_trans (le_max_left _ _) ht
    calc |α * t + r.im| ≤ |α * t| + |r.im| := abs_add_le _ _
      _ ≤ (α + |r.im|) * |t| := by
        rw [hat]; nlinarith [abs_nonneg r.im]
  have key := hR _ hu_ge
  rw [show 4 * α + r.re - (-3 * α + r.re) = 7 * α by ring] at key
  set g := Complex.Gamma (((-3 * α + r.re : ℝ) : ℂ) +
    ((α * t + r.im : ℝ) : ℂ) * Complex.I)
  have hgg : ‖g‖ * ‖g⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    by_cases h : ‖g‖ = 0
    · simp [h]
    · rw [mul_inv_cancel₀ h]
  have hpow : |α * t + r.im| ^ (7 * α) ≤
      (α + |r.im|) ^ (7 * α) * |t| ^ (7 * α) := by
    rw [← Real.mul_rpow hK.le (abs_nonneg _)]
    exact Real.rpow_le_rpow (abs_nonneg _) hu_le (by positivity)
  have hp0 : 0 ≤ |α * t + r.im| ^ (7 * α) := by positivity
  calc _ ≤ 3 * |α * t + r.im| ^ (7 * α) * ‖g‖ * ‖g⁻¹‖ :=
        mul_le_mul_of_nonneg_right key (norm_nonneg _)
    _ ≤ 3 * |α * t + r.im| ^ (7 * α) := by
        rw [mul_assoc]; exact mul_le_of_le_one_right (by positivity) hgg
    _ ≤ 3 * ((α + |r.im|) ^ (7 * α) * |t| ^ (7 * α)) := by gcongr
    _ = _ := by ring

open Complex in
/-- Polynomial growth of `F` on the line `Re s = -3`, from the functional equation and Stirling. -/
private lemma exists_norm_le_mul_rpow_line_neg_three (F : ℂ → ℂ) (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (D : FunctionalEquation F)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ s : ℂ, s.re = 4 → ‖F s‖ ≤ B) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ‖F (-3 + t * I)‖ ≤ C * |t| ^ (1 + ∑ i, 7 * D.α i) := by
  have hstir := fun i => norm_Gamma_line_four_mul_inv_line_neg_three_le (D.α i) (D.α_pos i) (D.r i)
  choose M T hM0 hMT using hstir
  set T₀ : ℝ := 1 + ∑ i, |T i| with hT₀
  have hT : ∀ i, T i ≤ T₀ := fun i => by
    have := Finset.single_le_sum (f := fun i => |T i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    have := le_abs_self (T i)
    linarith
  have hfe := FunctionalEquation.eq_of_re_lt_one hFd D
  have hQ := D.Q_pos
  set A : ℝ := 1 + ∑ i, 7 * D.α i with hAdef
  have hsumα : 0 ≤ ∑ i, 7 * D.α i := Finset.sum_nonneg fun i _ => by
    have := D.α_pos i; positivity
  have hM : 0 ≤ ∏ i, M i := Finset.prod_nonneg fun i _ => hM0 i
  refine ⟨D.Q ^ 7 * B * (∏ i, M i), T₀, by positivity, ?_⟩
  intro t ht
  have ht1 : 1 ≤ |t| := by
    have : 0 ≤ ∑ i, |T i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have ht0 : 0 < |t| := by linarith
  set s : ℂ := -3 + t * I with hs
  have hs' : 1 - starRingEnd ℂ s = 4 + t * I := by
    apply Complex.ext <;> simp [s]; norm_num
  have hsre : s.re = -3 := by simp [s]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsre; simp at hsre
  have h := congrArg norm (hfe s (by rw [hsre]; norm_num) hs0)
  rw [hs'] at h
  simp only [norm_mul, Complex.norm_conj, D.norm_w, one_mul, norm_prod, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ] at h
  have h4re : (4 + t * I : ℂ).re = 4 := by simp
  rw [Complex.neg_re, hsre, h4re] at h
  set Pr := ∏ i, (‖Complex.Gamma (D.α i * (4 + t * I) + D.r i)‖ *
      ‖(Complex.Gamma (D.α i * (-3 + t * I) + D.r i))⁻¹‖) with hPr
  have hX : ‖F s‖ = D.Q ^ 7 * ‖F (4 + t * I)‖ * Pr := by
    rw [h, hPr, Finset.prod_mul_distrib]
    simp only [norm_inv]
    have hQm : D.Q ^ (-(-3 : ℝ)) = D.Q ^ 3 := by
      rw [neg_neg, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hQ4 : D.Q ^ (4 : ℝ) = D.Q ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hQm, hQ4]
    ring
  have hPrb : Pr ≤ (∏ i, M i) * |t| ^ A := by
    calc Pr ≤ ∏ i, (M i * |t| ^ (7 * D.α i)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => hMT i t ((hT i).trans ht))
      _ = (∏ i, M i) * |t| ^ (∑ i, 7 * D.α i) := by
          rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht0]
      _ ≤ (∏ i, M i) * |t| ^ A := by
          gcongr
          linarith
  have hPr0 : 0 ≤ Pr := Finset.prod_nonneg fun i _ => by positivity
  have hF4 := hB (4 + t * I) h4re
  rw [hX]
  have : 0 < D.Q ^ 7 := by positivity
  calc D.Q ^ 7 * ‖F (4 + t * I)‖ * Pr ≤ D.Q ^ 7 * B * ((∏ i, M i) * |t| ^ A) := by
        gcongr
    _ = _ := by ring

open Complex in
/-- **Polynomial growth of `G = (s - 1)^m F` in the strip `-3 ≤ Re s ≤ σM`** (for `|Im s| ≥ 1`),
from the two edge bounds and Phragmén–Lindelöf. -/
private lemma exists_norm_le_mul_rpow_strip (F G : ℂ → ℂ) (m : ℕ) (β : ℝ) (hGd : Differentiable ℂ G)
    (hGo : HasGrowthOrderLE G β) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (D : FunctionalEquation F) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ s : ℂ, 2 ≤ s.re → ‖F s‖ ≤ B) (σM : ℝ) (hσM : 4 ≤ σM) :
    ∃ A C : ℝ, 0 ≤ A ∧
      ∀ s : ℂ, -3 ≤ s.re → s.re ≤ σM → 1 ≤ |s.im| → ‖G s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C0, T₀, hC0, hleft⟩ := exists_norm_le_mul_rpow_line_neg_three F hFd D B hB0 (fun s hs =>
      hB s (by linarith))
  set A0 : ℝ := 1 + ∑ i, 7 * D.α i with hA0
  have hsumα : 0 ≤ ∑ i, 7 * D.α i := Finset.sum_nonneg fun i _ => by
    have := D.α_pos i; positivity
  have hA0p : 1 ≤ A0 := by linarith
  set A : ℝ := m + A0 with hA
  obtain ⟨Bc, hBc⟩ := (isCompact_closedBall (0 : ℂ) (|T₀| + 4)).exists_bound_of_continuousOn
    hGd.continuous.continuousOn
  set CL : ℝ := max (max (5 ^ m * C0) |Bc|) ((σM + 1) ^ m * B) with hCL
  have hCL0 : 0 ≤ CL := le_trans (abs_nonneg _) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hpowA : ∀ t : ℝ, 1 ≤ |t| → (|t| ^ m * |t| ^ A0 = |t| ^ A) := by
    intro t ht
    have := Real.rpow_add (show (0:ℝ) < |t| by linarith) (m : ℝ) A0
    rw [Real.rpow_natCast] at this
    rw [hA, this]
  have hlines : ∃ C, ∀ s : ℂ, (s.re = -3 ∨ s.re = σM) → 1 ≤ |s.im| →
      ‖G s‖ ≤ C * |s.im| ^ A := by
    refine ⟨CL, fun s hs ht => ?_⟩
    have ht0 : 0 < |s.im| := by linarith
    have hpow1 : 1 ≤ |s.im| ^ A := Real.one_le_rpow ht (by positivity)
    have hs1 : s ≠ 1 := by
      rintro rfl; norm_num at ht
    rcases hs with hs | hs
    · have hse : s = -3 + (s.im : ℂ) * I := by
        apply Complex.ext <;> simp [hs]
      rcases le_or_gt T₀ |s.im| with hT0 | hT0
      · have hF := hleft s.im hT0
        rw [← hse] at hF
        have hn : ‖s - 1‖ ≤ 5 * |s.im| := by
          have := Complex.norm_le_abs_re_add_abs_im (s - 1)
          simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
            hs] at this
          norm_num at this
          linarith
        rw [hGF s hs1, norm_mul, norm_pow]
        calc ‖s - 1‖ ^ m * ‖F s‖ ≤ (5 * |s.im|) ^ m * (C0 * |s.im| ^ A0) := by gcongr
          _ = 5 ^ m * C0 * (|s.im| ^ m * |s.im| ^ A0) := by rw [mul_pow]; ring
          _ = 5 ^ m * C0 * |s.im| ^ A := by rw [hpowA _ ht]
          _ ≤ CL * |s.im| ^ A := by
            gcongr
            exact le_trans (le_max_left _ _) (le_max_left _ _)
      · have hmem : s ∈ Metric.closedBall (0 : ℂ) (|T₀| + 4) := by
          rw [mem_closedBall_zero_iff]
          have h1 := Complex.norm_le_abs_re_add_abs_im s
          rw [hs] at h1
          norm_num at h1
          have := le_abs_self T₀
          linarith
        calc ‖G s‖ ≤ Bc := hBc s hmem
          _ ≤ |Bc| := le_abs_self _
          _ ≤ CL := le_trans (le_max_right _ _) (le_max_left _ _)
          _ ≤ CL * |s.im| ^ A := le_mul_of_one_le_right hCL0 hpow1
    · have hn : ‖s - 1‖ ≤ (σM + 1) * |s.im| := by
        have := Complex.norm_le_abs_re_add_abs_im (s - 1)
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
          hs] at this
        rw [abs_of_nonneg (by linarith)] at this
        have h1 : σM ≤ σM * |s.im| := le_mul_of_one_le_right (by linarith) ht
        have e : (σM + 1) * |s.im| = σM * |s.im| + |s.im| := by ring
        rw [e]; linarith
      rw [hGF s hs1, norm_mul, norm_pow]
      have hmA : |s.im| ^ (m : ℝ) ≤ |s.im| ^ A :=
        Real.rpow_le_rpow_of_exponent_le ht (by rw [hA]; linarith)
      rw [Real.rpow_natCast] at hmA
      calc ‖s - 1‖ ^ m * ‖F s‖ ≤ ((σM + 1) * |s.im|) ^ m * B := by
            gcongr
            exact hB s (by rw [hs]; linarith)
        _ = (σM + 1) ^ m * B * |s.im| ^ m := by rw [mul_pow]; ring
        _ ≤ (σM + 1) ^ m * B * |s.im| ^ A :=
          mul_le_mul_of_nonneg_left hmA (by positivity)
        _ ≤ CL * |s.im| ^ A := by
          gcongr
          exact le_max_right _ _
  obtain ⟨C, hC⟩ := PhragmenLindelof.vertical_strip_le_mul_rpow hGd.diffContOnCl
    (Complex.HasGrowthOrderLE.exists_norm_le_exp_strip hGo (-3) σM (by linarith))
    hlines
  exact ⟨A, C, by rw [hA]; positivity, hC⟩

/-! ### Landau's lemma and good heights -/

open Complex Metric in
/-- Schwarz-type bound: `w(c) = 0` and `‖w‖ ≤ 1` on the circle give `‖w z‖ ≤ ‖z - c‖ / ρ`. -/
private lemma norm_le_dist_div_of_map_ball {w : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ w (closedBall c ρ)) (hw0 : w c = 0)
    (hb : ∀ z ∈ sphere c ρ, ‖w z‖ ≤ 1) :
    ∀ z ∈ closedBall c ρ, ‖w z‖ ≤ ‖z - c‖ / ρ := by
  have hq : DifferentiableOn ℂ (dslope w c) (closedBall c ρ) :=
    (Complex.differentiableOn_dslope (closedBall_mem_nhds c hρ)).2 hd
  have hqb : ∀ z ∈ frontier (ball c ρ), ‖dslope w c z‖ ≤ 1 / ρ := by
    intro z hz
    have hz' : z ∈ sphere c ρ := frontier_ball_subset_sphere hz
    have hzc : z ≠ c := ne_of_mem_sphere hz' hρ.ne'
    have hzn : ‖z - c‖ = ρ := by rwa [mem_sphere_iff_norm] at hz'
    rw [dslope_of_ne _ hzc, slope_def_module, hw0, sub_zero, norm_smul, norm_inv, hzn]
    have := hb z hz'
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right this hρ.le
  intro z hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hq.diffContOnCl_ball subset_rfl) hqb (by rwa [closure_ball c hρ.ne'])
  have e : w z = (z - c) * dslope w c z := by
    have := sub_smul_dslope w c z
    rw [hw0, sub_zero, smul_eq_mul] at this
    exact this.symm
  rw [e, norm_mul]
  calc ‖z - c‖ * ‖dslope w c z‖ ≤ ‖z - c‖ * (1 / ρ) :=
        mul_le_mul_of_nonneg_left hmax (norm_nonneg _)
    _ = ‖z - c‖ / ρ := by ring

open Complex Metric in
/-- Borel–Carathéodory (closed-ball form, `h c = 0`). -/
private lemma norm_le_of_re_le_closedBall {h : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hd : DifferentiableOn ℂ h (closedBall c ρ)) (hc : h c = 0)
    (hre : ∀ z ∈ closedBall c ρ, (h z).re ≤ M) :
    ∀ z ∈ ball c ρ, ‖h z‖ ≤ 2 * M * ‖z - c‖ / (ρ - ‖z - c‖) := by
  have hden : ∀ z ∈ closedBall c ρ, (2 * M : ℂ) - h z ≠ 0 := by
    intro z hz h0
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.zero_re] at this
    have h2 : ((2 * M : ℂ)).re = 2 * M := by simp
    rw [h2] at this
    have := hre z hz
    linarith
  have hnorm : ∀ z ∈ closedBall c ρ, ‖h z‖ ≤ ‖(2 * M : ℂ) - h z‖ := by
    intro z hz
    have hr := hre z hz
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    have h2 : ((2 * M : ℂ)).re = 2 * M := by simp
    have h3 : ((2 * M : ℂ)).im = 0 := by simp
    rw [h2, h3]
    nlinarith
  set w : ℂ → ℂ := fun z => h z / ((2 * M : ℂ) - h z) with hw
  have hwd : DifferentiableOn ℂ w (closedBall c ρ) :=
    hd.div ((differentiableOn_const _).sub hd) hden
  have hw0 : w c = 0 := by simp [hw, hc]
  have hw1 : ∀ z ∈ closedBall c ρ, ‖w z‖ ≤ 1 := by
    intro z hz
    simp only [hw, norm_div]
    rcases eq_or_ne ‖(2 * M : ℂ) - h z‖ 0 with h0 | h0
    · rw [h0, div_zero]; norm_num
    · rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
      exact hnorm z hz
  have hsch := norm_le_dist_div_of_map_ball hρ hwd hw0 (fun z hz => hw1 z (sphere_subset_closedBall
      hz))
  intro z hz
  have hzc : ‖z - c‖ < ρ := by rwa [mem_ball_iff_norm] at hz
  have hzc' : z ∈ closedBall c ρ := ball_subset_closedBall hz
  have hwz := hsch z hzc'
  have hwlt : ‖w z‖ < 1 := lt_of_le_of_lt hwz (by rw [div_lt_one hρ]; exact hzc)
  have hden' := hden z hzc'
  -- h = 2 M w / (1 + w)
  have hone : (1 : ℂ) + w z ≠ 0 := by
    intro h0
    have : w z = -1 := by linear_combination h0
    rw [this, norm_neg, norm_one] at hwlt
    exact lt_irrefl _ hwlt
  have hinv : h z = 2 * M * w z / (1 + w z) := by
    rw [eq_div_iff hone]
    simp only [hw]
    field_simp
    ring
  have hn1 : 1 - ‖w z‖ ≤ ‖1 + w z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-w z)
    simpa [sub_neg_eq_add] using this
  rw [hinv, norm_div, norm_mul, norm_mul]
  have h2M : ‖(2 : ℂ)‖ * ‖(M : ℂ)‖ = 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]; norm_num
  rw [h2M]
  have hpos : 0 < 1 - ‖w z‖ := by linarith
  have hρz : 0 < ρ - ‖z - c‖ := by linarith
  calc 2 * M * ‖w z‖ / ‖1 + w z‖ ≤ 2 * M * ‖w z‖ / (1 - ‖w z‖) := by
        apply div_le_div_of_nonneg_left (by positivity) hpos hn1
    _ ≤ 2 * M * (‖z - c‖ / ρ) / (1 - ‖z - c‖ / ρ) := by
        apply div_le_div₀ (by positivity) (by gcongr) (by
          rw [sub_pos, div_lt_one hρ]; exact hzc) (by linarith)
    _ = 2 * M * ‖z - c‖ / (ρ - ‖z - c‖) := by
        field_simp

open Complex Metric in
/-- A logarithm of a zero-free holomorphic function on a ball. -/
private lemma exists_log_of_ne_zero_ball {g : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (ball c ρ)) (hne : ∀ z ∈ ball c ρ, g z ≠ 0) :
    ∃ L : ℂ → ℂ, (∀ z ∈ ball c ρ, HasDerivAt L (deriv g z / g z) z) ∧ L c = 0 ∧
      ∀ z ∈ ball c ρ, g z = g c * Complex.exp (L z) := by
  have hA : AnalyticOnNhd ℂ g (ball c ρ) := hd.analyticOnNhd isOpen_ball
  have hq : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c ρ) :=
    hA.deriv.differentiableOn.div hd hne
  obtain ⟨L, hL0, hL⟩ := (hq.isExactOn_ball).with_val_at c 0
  refine ⟨L, hL, hL0, ?_⟩
  set k : ℂ → ℂ := fun z => g z * Complex.exp (-L z) with hk
  have hkd : ∀ z ∈ ball c ρ, HasDerivAt k 0 z := by
    intro z hz
    have hg : HasDerivAt g (deriv g z) z :=
      (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have he := ((hL z hz).neg).cexp
    have := hg.mul he
    refine this.congr_deriv ?_
    have := hne z hz
    field_simp
    ring
  have hkdiff : DifferentiableOn ℂ k (ball c ρ) := fun z hz =>
    (hkd z hz).differentiableAt.differentiableWithinAt
  have hconst : ∀ z ∈ ball c ρ, k z = k c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c ρ).isPreconnected hkdiff
      (fun x hx => (hkd x hx).deriv) hz (mem_ball_self hρ)
  intro z hz
  have h1 := hconst z hz
  simp only [hk, hL0, neg_zero, Complex.exp_zero, mul_one] at h1
  have : g z = g z * Complex.exp (-L z) * Complex.exp (L z) := by
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [this, h1]

private lemma differentiable_multiset_prod_sub (S : Multiset ℂ) :
    Differentiable ℂ (fun z => (S.map fun σ => z - σ).prod) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons σ S ih =>
    have e : (fun z => ((σ ::ₘ S).map fun σ => z - σ).prod) =
        fun z => (z - σ) * (S.map fun σ => z - σ).prod := by
      funext z; simp
    rw [e]
    exact (differentiable_id.sub_const σ).mul ih

private lemma analyticOrderAt_sub_const (σ ρ : ℂ) :
    analyticOrderAt (fun z : ℂ => z - σ) ρ = if ρ = σ then 1 else 0 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z - σ) ρ := by fun_prop
  split_ifs with h
  · subst h
    have : analyticOrderAt (fun z : ℂ => z - ρ) ρ = ((1 : ℕ) : ℕ∞) := by
      rw [ha.analyticOrderAt_eq_natCast]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero,
        Filter.Eventually.of_forall fun z => by simp⟩
    simp
  · rw [ha.analyticOrderAt_eq_zero]
    exact sub_ne_zero.2 h

private lemma analyticOrderAt_multiset_prod_sub (S : Multiset ℂ) (ρ : ℂ) :
    analyticOrderAt (fun z => (S.map fun σ => z - σ).prod) ρ = (S.count ρ : ℕ∞) := by
  classical
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.count_zero, Nat.cast_zero]
    exact (analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero
  | cons σ S ih =>
    have e : (fun z => ((σ ::ₘ S).map fun σ => z - σ).prod) =
        (fun z : ℂ => z - σ) * fun z => (S.map fun σ => z - σ).prod := by
      funext z; simp
    rw [e, analyticOrderAt_mul (by fun_prop) ((differentiable_multiset_prod_sub S).analyticAt ρ),
        ih,
      analyticOrderAt_sub_const, Multiset.count_cons]
    split_ifs <;> push_cast <;> ring

/-- Dividing out a multiset of zeros of an entire function. -/
private lemma exists_eq_multiset_prod_sub_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (S : Multiset ℂ)
    (hord : ∀ ρ, (S.count ρ : ℕ∞) ≤ analyticOrderAt f ρ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = (S.map fun σ => z - σ).prod * g z := by
  classical
  induction S using Multiset.induction_on with
  | empty => exact ⟨f, hf, fun z => by simp⟩
  | cons ρ S ih =>
    obtain ⟨g', hg', hfg⟩ := ih (fun σ => le_trans (by
      exact_mod_cast Multiset.count_le_of_le σ (Multiset.le_cons_self S ρ)) (hord σ))
    have hg'ρ : g' ρ = 0 := by
      by_contra h
      have hfe : f = (fun z => (S.map fun σ => z - σ).prod) * g' := funext hfg
      have h1 : analyticOrderAt f ρ =
          analyticOrderAt (fun z => (S.map fun σ => z - σ).prod) ρ + analyticOrderAt g' ρ := by
        rw [hfe]
        exact analyticOrderAt_mul ((differentiable_multiset_prod_sub S).analyticAt ρ)
            (hg'.analyticAt ρ)
      rw [analyticOrderAt_multiset_prod_sub, (hg'.analyticAt ρ).analyticOrderAt_eq_zero.mpr h,
          add_zero] at h1
      have h2 := hord ρ
      rw [h1, Multiset.count_cons_self] at h2
      have : S.count ρ + 1 ≤ S.count ρ := by exact_mod_cast h2
      omega
    refine ⟨dslope g' ρ, ?_, fun z => ?_⟩
    · exact differentiableOn_univ.1
        ((Complex.differentiableOn_dslope Filter.univ_mem).2 hg'.differentiableOn)
    · have := sub_smul_dslope g' ρ z
      rw [hg'ρ, sub_zero, smul_eq_mul] at this
      rw [hfg z, Multiset.map_cons, Multiset.prod_cons, ← this]
      ring

private lemma prod_pow_eq_multiset_prod_replicate (Z : Finset ℂ) (k : ℂ → ℕ) (z : ℂ) :
    ((∑ ρ ∈ Z, Multiset.replicate (k ρ) ρ).map fun σ => z - σ).prod =
      ∏ ρ ∈ Z, (z - ρ) ^ (k ρ) := by
  classical
  induction Z using Finset.induction_on with
  | empty => simp
  | insert a Z ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih,
      Multiset.map_replicate, Multiset.prod_replicate]

private lemma count_bind_replicate (Z : Finset ℂ) (k : ℂ → ℕ) (σ : ℂ) :
    (∑ ρ ∈ Z, Multiset.replicate (k ρ) ρ).count σ = if σ ∈ Z then k σ else 0 := by
  classical
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq']

/-- Factor out the zeros of an entire function in a closed disc. -/
private lemma exists_eq_prod_zeros_mul_closedBall {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (hfc : f c ≠ 0) (r : ℝ) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, f ρ = 0 ∧ ‖ρ - c‖ ≤ r) ∧ (∀ ρ, ‖ρ - c‖ ≤ r → f ρ = 0 → ρ ∈ Z) ∧
      ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
        (∀ z, f z = (∏ ρ ∈ Z, (z - ρ) ^ (analyticOrderNatAt f ρ)) * g z) ∧
        (∀ z, ‖z - c‖ ≤ r → g z ≠ 0) := by
  classical
  have hfin : {ρ : ℂ | f ρ = 0 ∧ ‖ρ - c‖ ≤ r}.Finite :=
    (Complex.finite_setOf_eq_zero_norm_le hf hfc (‖c‖ + r)).subset fun ρ hρ =>
      ⟨hρ.1, by
        have := norm_le_norm_add_norm_sub' ρ c
        linarith [hρ.2]⟩
  set Z := hfin.toFinset with hZdef
  have hZ : ∀ ρ, ρ ∈ Z ↔ f ρ = 0 ∧ ‖ρ - c‖ ≤ r := fun ρ => by simp [Z]
  set k : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ with hkdef
  have hfin_ord : ∀ ρ, analyticOrderAt f ρ ≠ ⊤ := Complex.analyticOrderAt_ne_top_of_differentiable
      hf hfc
  have hk : ∀ ρ, (k ρ : ℕ∞) = analyticOrderAt f ρ := fun ρ => by
    simp only [k, analyticOrderNatAt]
    exact ENat.natCast_toNat (hfin_ord ρ)
  set S := ∑ ρ ∈ Z, Multiset.replicate (k ρ) ρ with hS
  obtain ⟨g, hg, hfg⟩ := exists_eq_multiset_prod_sub_mul hf S (fun σ => by
    rw [count_bind_replicate]
    split_ifs
    · rw [hk]
    · simp)
  have hP : ∀ z, (S.map fun σ => z - σ).prod = ∏ ρ ∈ Z, (z - ρ) ^ (k ρ) :=
    prod_pow_eq_multiset_prod_replicate Z k
  refine ⟨Z, fun ρ hρ => (hZ ρ).1 hρ, fun ρ h1 h2 => (hZ ρ).2 ⟨h2, h1⟩, g, hg,
    fun z => by rw [hfg z, hP z], ?_⟩
  intro z hz hgz
  by_cases hfz : f z = 0
  · have hzZ : z ∈ Z := (hZ z).2 ⟨hfz, hz⟩
    have hfe : f = (fun z => (S.map fun σ => z - σ).prod) * g := funext hfg
    have h1 : analyticOrderAt f z =
        analyticOrderAt (fun z => (S.map fun σ => z - σ).prod) z + analyticOrderAt g z := by
      rw [hfe]; exact analyticOrderAt_mul ((differentiable_multiset_prod_sub S).analyticAt z)
          (hg.analyticAt z)
    rw [analyticOrderAt_multiset_prod_sub, count_bind_replicate, ite_eq_left hzZ, ← hk z] at h1
    have h0 : analyticOrderAt g z ≠ 0 := by
      rw [Ne, (hg.analyticAt z).analyticOrderAt_eq_zero, not_not]; exact hgz
    revert h1 h0
    induction analyticOrderAt g z using ENat.recTopCoe with
    | top => intro h1 _; simp at h1
    | coe n =>
      intro h1 h0
      have : k z = k z + n := by exact_mod_cast h1
      have hn : n ≠ 0 := by exact_mod_cast h0
      omega
  · exact hfz (by rw [hfg z, hgz, mul_zero])

open Complex Metric in
/-- **Landau's lemma.** For an entire `f` with `‖f‖ ≤ M ‖f c‖` on the circle `‖z - c‖ = 5`,
`f'/f` is the sum over the zeros within `9/4` of `c` up to `O(log M)` in `‖z - c‖ ≤ 8/5`, and
those zeros number `O(log M)`. -/
private lemma norm_logDeriv_sub_sum_zeros_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {M : ℝ}
    (hM : 1 ≤ M)
    (hfc : f c ≠ 0) (hbd : ∀ z ∈ sphere c 5, ‖f z‖ ≤ M * ‖f c‖) :
    ∃ Z : Finset ℂ, (∀ ρ ∈ Z, f ρ = 0 ∧ ‖ρ - c‖ ≤ 9 / 4) ∧
      (∀ ρ, ‖ρ - c‖ ≤ 9 / 4 → f ρ = 0 → ρ ∈ Z) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * Real.log (11 / 9) ≤ Real.log M ∧
      ∀ z, ‖z - c‖ ≤ 8 / 5 → f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
          90 * (Real.log M + 1) := by
  classical
  obtain ⟨Z, hZ1, hZ2, g, hg, hfg, hg0⟩ := exists_eq_prod_zeros_mul_closedBall hf hfc (9 / 4)
  set k : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ with hk
  set N : ℕ := ∑ ρ ∈ Z, k ρ with hN
  set P : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (z - ρ) ^ (k ρ) with hP
  have hfg' : ∀ z, f z = P z * g z := hfg
  have hPnorm : ∀ z, ‖P z‖ = ∏ ρ ∈ Z, ‖z - ρ‖ ^ (k ρ) := fun z => by
    simp only [P, norm_prod, norm_pow]
  have hPc : ‖P c‖ ≤ (9 / 4) ^ N := by
    rw [hPnorm, hN, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ =>
      pow_le_pow_left₀ (norm_nonneg _) (by rw [norm_sub_rev]; exact (hZ1 ρ hρ).2) _
  have hPs : ∀ z ∈ sphere c 5, (11 / 4) ^ N ≤ ‖P z‖ := by
    intro z hz
    rw [hPnorm, hN, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun ρ hρ =>
      pow_le_pow_left₀ (by norm_num) ?_ _
    have h1 : ‖z - c‖ = 5 := by rwa [mem_sphere_iff_norm] at hz
    have h2 := (hZ1 ρ hρ).2
    have := norm_sub_norm_le (z - c) (ρ - c)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have hgc : g c ≠ 0 := hg0 c (by norm_num)
  have hfc0 : 0 < ‖f c‖ := norm_pos_iff.2 hfc
  have hPc0 : P c ≠ 0 := fun h => hfc (by rw [hfg' c, h, zero_mul])
  have hPc0' : 0 < ‖P c‖ := norm_pos_iff.2 hPc0
  have h94 : (0 : ℝ) < (9 / 4) ^ N := by positivity
  have h114 : (0 : ℝ) < (11 / 4) ^ N := by positivity
  -- the bound for `g` on the circle and in the disc
  have hgs : ∀ z ∈ sphere c 5, ‖g z‖ ≤ M * ‖f c‖ / (11 / 4) ^ N := by
    intro z hz
    have hPz := hPs z hz
    have hPz0 : 0 < ‖P z‖ := lt_of_lt_of_le h114 hPz
    have e : ‖g z‖ = ‖f z‖ / ‖P z‖ := by
      rw [hfg' z, norm_mul, mul_div_cancel_left₀ _ hPz0.ne']
    rw [e]
    calc ‖f z‖ / ‖P z‖ ≤ M * ‖f c‖ / ‖P z‖ := div_le_div_of_nonneg_right (hbd z hz) hPz0.le
      _ ≤ M * ‖f c‖ / (11 / 4) ^ N := div_le_div_of_nonneg_left (by positivity) h114 hPz
  have hgmax : ∀ w ∈ closedBall c 5, ‖g w‖ ≤ M * ‖f c‖ / (11 / 4) ^ N := by
    intro w hw
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hg.differentiableOn.diffContOnCl_ball subset_rfl)
      (fun z hz => hgs z (frontier_ball_subset_sphere hz))
      (by rwa [closure_ball c (by norm_num)])
  have hgc' : ‖f c‖ / (9 / 4) ^ N ≤ ‖g c‖ := by
    have e : ‖g c‖ = ‖f c‖ / ‖P c‖ := by
      rw [hfg' c, norm_mul, mul_div_cancel_left₀ _ hPc0'.ne']
    rw [e]
    exact div_le_div_of_nonneg_left hfc0.le hPc0' hPc
  have hgcb := hgmax c (by simp)
  -- the zero count
  have hcount : ((11 / 9 : ℝ)) ^ N ≤ M := by
    have h1 : ‖f c‖ / (9 / 4) ^ N ≤ M * ‖f c‖ / (11 / 4) ^ N := hgc'.trans hgcb
    rw [div_le_div_iff₀ h94 h114] at h1
    have h2 : (11 / 4 : ℝ) ^ N ≤ M * (9 / 4) ^ N := by nlinarith
    have e : (11 / 9 : ℝ) ^ N = (11 / 4) ^ N / (9 / 4) ^ N := by
      rw [← div_pow]; norm_num
    rw [e, div_le_iff₀ h94]
    exact h2
  have hcount' : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * Real.log (11 / 9) ≤ Real.log M := by
    have hNr : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) = (N : ℝ) := by
      simp only [hN, k, Nat.cast_sum]
    rw [hNr, ← Real.log_pow]
    exact Real.log_le_log (by positivity) hcount
  -- `‖g‖ ≤ M ‖g c‖` in the disc
  have hgle : ∀ w ∈ closedBall c 5, ‖g w‖ ≤ M * ‖g c‖ := by
    intro w hw
    refine (hgmax w hw).trans ?_
    calc M * ‖f c‖ / (11 / 4) ^ N ≤ M * ‖f c‖ / (9 / 4) ^ N := by
          apply div_le_div_of_nonneg_left (by positivity) h94
          exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = M * (‖f c‖ / (9 / 4) ^ N) := by ring
      _ ≤ M * ‖g c‖ := by gcongr
  -- the logarithm of `g / g c`
  have hgne : ∀ z ∈ ball c (9 / 4), g z ≠ 0 := fun z hz =>
    hg0 z (by rw [mem_ball_iff_norm] at hz; exact hz.le)
  obtain ⟨L, hLd, hL0, hLe⟩ := exists_log_of_ne_zero_ball (by norm_num) hg.differentiableOn hgne
  have hLdiff : DifferentiableOn ℂ L (ball c (9 / 4)) := fun z hz =>
    (hLd z hz).differentiableAt.differentiableWithinAt
  have hsub2 : closedBall c 2 ⊆ ball c (9 / 4) := closedBall_subset_ball (by norm_num)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hreL : ∀ w ∈ closedBall c 2, (L w).re ≤ Real.log M + 1 := by
    intro w hw
    have hw' := hsub2 hw
    have h1 := hLe w hw'
    have h2 : ‖g w‖ = ‖g c‖ * Real.exp (L w).re := by
      rw [h1, norm_mul, Complex.norm_exp]
    have h3 := hgle w (closedBall_subset_closedBall (by norm_num) hw)
    rw [h2] at h3
    have hgc0 : 0 < ‖g c‖ := norm_pos_iff.2 hgc
    have h4 : Real.exp (L w).re ≤ M := by
      have := (mul_le_mul_iff_of_pos_left hgc0).1 (by linarith : ‖g c‖ * Real.exp (L w).re ≤ ‖g c‖
          * M)
      exact this
    have h5 : (L w).re ≤ Real.log M := by
      rw [← Real.log_exp (L w).re]
      exact Real.log_le_log (Real.exp_pos _) h4
    linarith
  have hbc := norm_le_of_re_le_closedBall (h := L) (c := c) (ρ := 2) (M := Real.log M + 1) (by
      norm_num)
    (by linarith) (hLdiff.mono hsub2) hL0 hreL
  have hLb : ∀ w, ‖w - c‖ ≤ 9 / 5 → ‖L w‖ ≤ 18 * (Real.log M + 1) := by
    intro w hw
    have hwb : w ∈ ball c 2 := by rw [mem_ball_iff_norm]; linarith
    refine (hbc w hwb).trans ?_
    have hpos : 0 < 2 - ‖w - c‖ := by linarith
    rw [div_le_iff₀ hpos]
    have h0 : 0 ≤ ‖w - c‖ := norm_nonneg _
    nlinarith
  refine ⟨Z, hZ1, hZ2, hcount', fun z hz hfz => ?_⟩
  have hzb : z ∈ ball c (9 / 4) := by rw [mem_ball_iff_norm]; linarith
  -- Cauchy's estimate for `L'`
  have hcl : closedBall z (1 / 5) ⊆ ball c (9 / 4) := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [mem_ball_iff_norm]
    have := norm_sub_le_norm_sub_add_norm_sub w z c
    linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1 / 5)
    (C := 18 * (Real.log M + 1)) (by norm_num) (hLdiff.diffContOnCl_ball hcl) (fun w hw => by
      apply hLb
      rw [mem_sphere_iff_norm] at hw
      have := norm_sub_le_norm_sub_add_norm_sub w z c
      linarith)
  rw [(hLd z hzb).deriv] at hcauchy
  -- the log-derivative split
  have hPz : P z ≠ 0 := fun h => hfz (by rw [hfg' z, h, zero_mul])
  have hgz : g z ≠ 0 := fun h => hfz (by rw [hfg' z, h, mul_zero])
  have hfe : f = fun z => P z * g z := funext hfg'
  have hPd : DifferentiableAt ℂ P z := by
    simp only [P]
    exact DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub_const ρ).pow _
  have hsplit : deriv f z / f z = logDeriv P z + deriv g z / g z := by
    rw [← logDeriv_apply, ← logDeriv_apply, hfe]
    exact logDeriv_fun_mul z hPz hgz hPd (hg z)
  have hfac : ∀ ρ ∈ Z, (z - ρ) ^ (k ρ) ≠ 0 := fun ρ hρ => by
    simp only [P] at hPz
    exact (Finset.prod_ne_zero_iff.1 hPz) ρ hρ
  have hlogP : logDeriv P z = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) := by
    simp only [P]
    rw [logDeriv_fun_prod hfac (fun ρ _ => (differentiableAt_id.sub_const ρ).pow _)]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [logDeriv_fun_pow (f := fun x : ℂ => x - ρ) (differentiableAt_id.sub_const ρ),
        logDeriv_apply]
    have hd : deriv (fun x : ℂ => x - ρ) z = 1 := by
      simp
    rw [hd]
    simp only [k]
    ring
  rw [hsplit, hlogP, add_sub_cancel_left]
  calc ‖deriv g z / g z‖ ≤ 18 * (Real.log M + 1) / (1 / 5) := hcauchy
    _ = 90 * (Real.log M + 1) := by ring

private lemma norm_le_of_sq_add_sq_le {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : w.re ^ 2 + w.im ^ 2 ≤ r ^
    2) :
    ‖w‖ ≤ r := by
  rw [← sq_le_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- Pigeonhole: some height in `(T, T + 1)` keeps distance `1 / (2 (#Y + 1))` from a finite set. -/
private lemma exists_far_from_finset (Y : Finset ℝ) (T : ℝ) :
    ∃ T' : ℝ, T < T' ∧ T' < T + 1 ∧ ∀ y ∈ Y, 1 / (2 * ((Y.card : ℝ) + 1)) ≤ |T' - y| := by
  classical
  set N := Y.card with hN
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  by_contra hcon
  push Not at hcon
  have hall : ∀ j ∈ Finset.range (N + 1), ∃ y ∈ Y,
      |T + ((j : ℝ) + 1 / 2) / (N + 1) - y| < 1 / (2 * ((N : ℝ) + 1)) := by
    intro j hj
    have hj' : (j : ℝ) + 1 ≤ N + 1 := by
      have := Finset.mem_range.1 hj
      exact_mod_cast this
    refine hcon _ ?_ ?_
    · have : 0 < ((j : ℝ) + 1 / 2) / (N + 1) := by positivity
      linarith
    · have : ((j : ℝ) + 1 / 2) / (N + 1) < 1 := by
        rw [div_lt_one hN1]; linarith
      linarith
  choose! φ hφY hφ using hall
  obtain ⟨j, hj, j', hj', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := Y) (by simp [N]) (fun j hj => hφY j hj)
  have h1 := hφ j hj
  have h2 := hφ j' hj'
  rw [heq] at h1
  have h3 : |(T + ((j : ℝ) + 1 / 2) / (N + 1)) - (T + ((j' : ℝ) + 1 / 2) / (N + 1))| <
      1 / ((N : ℝ) + 1) := by
    have := abs_sub_le (T + ((j : ℝ) + 1 / 2) / (N + 1)) (φ j')
      (T + ((j' : ℝ) + 1 / 2) / (N + 1))
    rw [abs_sub_comm (φ j')] at this
    have e : 1 / ((N : ℝ) + 1) = 1 / (2 * ((N : ℝ) + 1)) + 1 / (2 * ((N : ℝ) + 1)) := by
      field_simp; ring
    linarith
  have e : (T + ((j : ℝ) + 1 / 2) / (N + 1)) - (T + ((j' : ℝ) + 1 / 2) / (N + 1)) =
      ((j : ℝ) - j') / (N + 1) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hN1, div_lt_div_iff_of_pos_right hN1] at h3
  have h4 : (1 : ℝ) ≤ |(j : ℝ) - j'| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  linarith

open Complex Metric in
/-- Landau's lemma at height `t₀` for a function of polynomial growth in `-3 ≤ Re s ≤ 7` that is
bounded below on `Re s = 2`. -/
private lemma exists_logDeriv_local_expansion {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C κ : ℝ} (hA
    : 0 ≤ A)
    (hκ : 0 < κ)
    (hgrowth : ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 7 → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A)
    (hlow : ∀ s : ℂ, s.re = 2 → 1 ≤ |s.im| → κ ≤ ‖f s‖) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t₀ : ℝ, 8 ≤ |t₀| →
      ∃ Z : Finset ℂ, (∀ ρ ∈ Z, f ρ = 0 ∧ ‖ρ - (2 + t₀ * I)‖ ≤ 9 / 4) ∧
        (∀ ρ, ‖ρ - (2 + t₀ * I)‖ ≤ 9 / 4 → f ρ = 0 → ρ ∈ Z) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ K * Real.log |t₀| ∧
        ∀ z, ‖z - (2 + t₀ * I)‖ ≤ 8 / 5 → f z ≠ 0 →
          ‖deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤
            K * Real.log |t₀| := by
  set Lc : ℝ := Real.log (1 + (|C| + 1) / κ) with hLc
  have hLc0 : 0 ≤ Lc := Real.log_nonneg (by have : 0 ≤ (|C| + 1) / κ := (by positivity); linarith)
  have hl8 : 1 < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hl119 : 0 < Real.log (11 / 9) := Real.log_pos (by norm_num)
  set K0 : ℝ := Lc / Real.log 8 + 2 * A + 1 / Real.log 8 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨K0 * (90 + 1 / Real.log (11 / 9)), by positivity, fun t₀ ht₀ => ?_⟩
  set c : ℂ := 2 + t₀ * I with hc
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = t₀ := by simp [c]
  have hlt : Real.log 8 ≤ Real.log |t₀| := Real.log_le_log (by norm_num) ht₀
  have hlt0 : 0 < Real.log |t₀| := by linarith
  set M : ℝ := (1 + (|C| + 1) / κ) * (|t₀| + 5) ^ A with hM
  have hpowge : 1 ≤ (|t₀| + 5) ^ A := Real.one_le_rpow (by linarith) hA
  have hM1 : 1 ≤ M := by
    have : 1 ≤ 1 + (|C| + 1) / κ := by have : 0 ≤ (|C| + 1) / κ := (by positivity); linarith
    nlinarith
  have hfc : κ ≤ ‖f c‖ := hlow c hcre (by rw [hcim]; linarith)
  have hfc0 : f c ≠ 0 := fun h => by rw [h, norm_zero] at hfc; linarith
  have hbd : ∀ z ∈ sphere c 5, ‖f z‖ ≤ M * ‖f c‖ := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    have him := Complex.abs_im_le_norm (z - c)
    rw [hz, Complex.sub_re, hcre] at hre
    rw [hz, Complex.sub_im, hcim] at him
    have hre' := abs_le.1 hre
    have him1 : |t₀| - 5 ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub t₀ z.im
      rw [abs_sub_comm] at this; linarith
    have him2 : |z.im| ≤ |t₀| + 5 := by
      have := abs_sub_abs_le_abs_sub z.im t₀
      linarith
    have hg := hgrowth z (by linarith) (by linarith) (by linarith)
    calc ‖f z‖ ≤ C * |z.im| ^ A := hg
      _ ≤ |C| * (|t₀| + 5) ^ A := by
          calc C * |z.im| ^ A ≤ |C| * |z.im| ^ A :=
                mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
            _ ≤ |C| * (|t₀| + 5) ^ A := by gcongr
      _ ≤ M * κ := by
          rw [hM]
          have e : (1 + (|C| + 1) / κ) * (|t₀| + 5) ^ A * κ =
              (κ + |C| + 1) * (|t₀| + 5) ^ A := by field_simp; ring
          rw [e]
          nlinarith
      _ ≤ M * ‖f c‖ := by gcongr
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := norm_logDeriv_sub_sum_zeros_le hf hM1 hfc0 hbd
  -- `log M ≤ K0 log |t₀| - 1/log 8 * log |t₀|`
  have hlogM : Real.log M + 1 ≤ K0 * Real.log |t₀| := by
    have hpos1 : 0 < 1 + (|C| + 1) / κ := by positivity
    have e : Real.log M = Lc + A * Real.log (|t₀| + 5) := by
      rw [hM, Real.log_mul hpos1.ne' (by positivity), Real.log_rpow (by linarith)]
    have h5 : Real.log (|t₀| + 5) ≤ 2 * Real.log |t₀| := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log (by linarith)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      nlinarith
    have hLc' : Lc ≤ Lc / Real.log 8 * Real.log |t₀| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    have h1' : 1 ≤ 1 / Real.log 8 * Real.log |t₀| := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by linarith)]; linarith
    rw [e, hK0]
    nlinarith
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  refine ⟨Z, hZ1, hZ2, ?_, fun z hz hfz => ?_⟩
  · have h1 : (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ Real.log M / Real.log (11 / 9) := by
      rw [le_div_iff₀ hl119]; exact hZ3
    refine h1.trans ?_
    rw [div_le_iff₀ hl119]
    have : 0 ≤ K0 * Real.log |t₀| := by positivity
    have h2 : Real.log M ≤ K0 * Real.log |t₀| := by linarith
    calc Real.log M ≤ K0 * Real.log |t₀| := h2
      _ ≤ K0 * (90 + 1 / Real.log (11 / 9)) * Real.log |t₀| * Real.log (11 / 9) := by
          have e : K0 * (90 + 1 / Real.log (11 / 9)) * Real.log |t₀| * Real.log (11 / 9) =
              K0 * Real.log |t₀| * (90 * Real.log (11 / 9)) + K0 * Real.log |t₀| := by
            field_simp
          rw [e]
          have : 0 ≤ K0 * Real.log |t₀| * (90 * Real.log (11 / 9)) := by positivity
          linarith
  · refine (hZ4 z hz hfz).trans ?_
    have : 0 ≤ K0 * Real.log |t₀| * (1 / Real.log (11 / 9)) := by positivity
    calc 90 * (Real.log M + 1) ≤ 90 * (K0 * Real.log |t₀|) := by linarith
      _ ≤ K0 * (90 + 1 / Real.log (11 / 9)) * Real.log |t₀| := by
          have e : K0 * (90 + 1 / Real.log (11 / 9)) * Real.log |t₀| =
              90 * (K0 * Real.log |t₀|) + K0 * Real.log |t₀| * (1 / Real.log (11 / 9)) := by ring
          rw [e]; linarith

open Complex Metric in
/-- **Good heights.** For `f` as in `exists_logDeriv_local_expansion`, near every large height `±T`
    there are
`O(log T)` zeros with `0 ≤ Re ≤ 1`, and a height `T' ∈ (T, T + 1)` with
`f'/f(u ± iT') = O(log² T)` for `1/2 ≤ u ≤ 3/2`. -/
private lemma exists_good_height {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C κ : ℝ} (hA : 0 ≤ A)
    (hκ : 0 < κ)
    (hgrowth : ∀ s : ℂ, -3 ≤ s.re → s.re ≤ 7 → 1 ≤ |s.im| → ‖f s‖ ≤ C * |s.im| ^ A)
    (hlow : ∀ s : ℂ, s.re = 2 → 1 ≤ |s.im| → κ ≤ ‖f s‖) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 8 ≤ T → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∃ Z : Finset ℂ, (∀ ρ ∈ Z, f ρ = 0) ∧
        (∀ ρ, f ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → T ≤ ε * ρ.im → ε * ρ.im ≤ T + 1 → ρ ∈ Z) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ K * Real.log T) ∧
      ∃ T' : ℝ, T < T' ∧ T' < T + 1 ∧ ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 →
        f (u + ε * T' * I) ≠ 0 ∧
        ‖deriv f (u + ε * T' * I) / f (u + ε * T' * I)‖ ≤ K * Real.log T ^ 2 := by
  classical
  obtain ⟨K0, hK00, hloc⟩ := exists_logDeriv_local_expansion hf hA hκ hgrowth hlow
  refine ⟨8 * K0 ^ 2 + 8 * K0, by positivity, fun T hT ε hε => ?_⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set t₀ : ℝ := ε * (T + 1 / 2) with ht₀
  have ht₀a : |t₀| = T + 1 / 2 := by rw [ht₀, abs_mul, hεa, one_mul, abs_of_pos (by linarith)]
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := hloc t₀ (by rw [ht₀a]; linarith)
  rw [ht₀a] at hZ3 hZ4
  have hlT : 0 < Real.log T := Real.log_pos (by linarith)
  have hl8 : 1 < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hlT1 : 1 ≤ Real.log T := le_trans hl8.le (Real.log_le_log (by norm_num) hT)
  have hlog2 : Real.log (T + 1 / 2) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  set S : ℝ := ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hSb : S ≤ 2 * K0 * Real.log T := by
    refine hZ3.trans ?_
    have := mul_le_mul_of_nonneg_left hlog2 hK00
    linarith
  -- each zero has order at least one
  have hfin : ∀ ρ, analyticOrderAt f ρ ≠ ⊤ := by
    obtain ⟨-, -, -, -⟩ := hloc t₀ (by rw [ht₀a]; linarith)
    have hfc : f (2 + t₀ * I) ≠ 0 := by
      intro h0
      have := hlow (2 + t₀ * I) (by simp) (by
        simp only [add_im, im_ofNat, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
          mul_zero, add_zero, zero_add]
        rw [ht₀a]; linarith)
      rw [h0, norm_zero] at this; linarith
    exact Complex.analyticOrderAt_ne_top_of_differentiable hf hfc
  have hord1 : ∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ := by
    intro ρ hρ
    have h0 := (hZ1 ρ hρ).1
    have hne : analyticOrderAt f ρ ≠ 0 := by
      rw [Ne, (hf.analyticAt ρ).analyticOrderAt_eq_zero, not_not]; exact h0
    have := hfin ρ
    simp only [analyticOrderNatAt]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 this
    rw [← hn] at hne ⊢
    simp only [ENat.toNat_natCast]
    have : n ≠ 0 := by exact_mod_cast hne
    omega
  have hcard : (Z.card : ℝ) ≤ S := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, hS]
    exact Finset.sum_le_sum fun ρ hρ => by exact_mod_cast hord1 ρ hρ
  constructor
  · refine ⟨Z, fun ρ hρ => (hZ1 ρ hρ).1, fun ρ h0 h1 h2 h3 h4 => hZ2 ρ ?_ h0, ?_⟩
    · apply norm_le_of_sq_add_sq_le (by norm_num)
      have hre : (ρ - (2 + t₀ * I)).re = ρ.re - 2 := by simp
      have him : (ρ - (2 + t₀ * I)).im = ρ.im - t₀ := by simp
      rw [hre, him]
      have h5 : (ρ.im - t₀) ^ 2 = (ε * ρ.im - (T + 1 / 2)) ^ 2 := by
        have : (ε * ρ.im - (T + 1 / 2)) = ε * (ρ.im - t₀) := by
          rw [ht₀]; linear_combination (T + 1/2) * hε2
        rw [this, mul_pow, show ε ^ 2 = ε * ε by ring, hε2, one_mul]
      rw [h5]
      nlinarith
    · calc S ≤ 2 * K0 * Real.log T := hSb
        _ ≤ (8 * K0 ^ 2 + 8 * K0) * Real.log T := by
            have : 0 ≤ K0 ^ 2 * Real.log T := by positivity
            nlinarith
  · set Y : Finset ℝ := Z.image fun ρ => ε * ρ.im with hY
    obtain ⟨T', hT'1, hT'2, hT'Y⟩ := exists_far_from_finset Y T
    have hYc : (Y.card : ℝ) ≤ S := le_trans (by exact_mod_cast Finset.card_image_le) hcard
    refine ⟨T', hT'1, hT'2, fun u hu1 hu2 => ?_⟩
    set z : ℂ := u + ε * T' * I with hz
    have hzc : ‖z - (2 + t₀ * I)‖ ≤ 8 / 5 := by
      apply norm_le_of_sq_add_sq_le (by norm_num)
      have hre : (z - (2 + t₀ * I)).re = u - 2 := by simp [z]
      have him : (z - (2 + t₀ * I)).im = ε * (T' - (T + 1 / 2)) := by
        simp [z, ht₀]; ring
      rw [hre, him, mul_pow, show ε ^ 2 = ε * ε by ring, hε2, one_mul]
      nlinarith
    have hsep : ∀ ρ ∈ Z, 1 / (2 * (S + 1)) ≤ |(z - ρ).im| := by
      intro ρ hρ
      have hy : ε * ρ.im ∈ Y := Finset.mem_image.2 ⟨ρ, hρ, rfl⟩
      have h1 := hT'Y _ hy
      have him : |(z - ρ).im| = |T' - ε * ρ.im| := by
        have h0 : (z - ρ).im = ε * T' - ρ.im := by simp [z]
        have : (z - ρ).im = ε * (T' - ε * ρ.im) := by
          rw [h0]; linear_combination ρ.im * hε2
        rw [this, abs_mul, hεa, one_mul]
      rw [him]
      refine le_trans ?_ h1
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hfz : f z ≠ 0 := by
      intro h0
      have hzZ := hZ2 z (le_trans hzc (by norm_num)) h0
      have := hsep z hzZ
      rw [sub_self, Complex.zero_im, abs_zero] at this
      have : 0 < 1 / (2 * (S + 1)) := by positivity
      linarith
    refine ⟨hfz, ?_⟩
    have hsum : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ S * (2 * (S + 1)) := by
      refine (norm_sum_le _ _).trans ?_
      rw [hS, Finset.sum_mul]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      rw [norm_div, Complex.norm_natCast]
      have h1 := hsep ρ hρ
      have h2 : |(z - ρ).im| ≤ ‖z - ρ‖ := Complex.abs_im_le_norm _
      have hpos : 0 < 1 / (2 * (S + 1)) := by positivity
      have hzρ : 0 < ‖z - ρ‖ := by linarith
      rw [div_le_iff₀ hzρ]
      have h3 : 1 ≤ 2 * (S + 1) * ‖z - ρ‖ := by
        have := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0:ℝ) ≤ 2 * (S + 1))
        rwa [mul_one_div_cancel (by positivity)] at this
      have h4 : (0 : ℝ) ≤ analyticOrderNatAt f ρ := Nat.cast_nonneg _
      nlinarith
    have h1 := hZ4 z hzc hfz
    calc ‖deriv f z / f z‖
        ≤ ‖deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ +
          ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ := norm_le_norm_sub_add _ _
      _ ≤ K0 * Real.log (T + 1 / 2) + S * (2 * (S + 1)) := add_le_add h1 hsum
      _ ≤ K0 * (2 * Real.log T) + 2 * K0 * Real.log T * (2 * (2 * K0 * Real.log T + 1)) := by
          gcongr
      _ ≤ (8 * K0 ^ 2 + 8 * K0) * Real.log T ^ 2 := by
          have h1 : K0 * Real.log T ≤ K0 * Real.log T ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hK00
            nlinarith
          nlinarith

/-! ### Oscillatory integrals on `Re s = 3/2` -/

open MeasureTheory in
/-- Interchange of a vertical Dirichlet series with a bounded continuous kernel on `[A, B]`. -/
private lemma hasSum_intervalIntegral_term_mul {a : ℕ → ℂ} {c : ℝ}
    (h : LSeriesSummable a (c : ℂ)) {K : ℝ → ℂ} (hK : Continuous K) {M : ℝ}
    (hKB : ∀ t, ‖K t‖ ≤ M) (A B : ℝ) :
    HasSum (fun n => ∫ t in A..B, LSeries.term a ((c : ℂ) + (t : ℂ) * Complex.I) n * K t)
      (∫ t in A..B, LSeries a ((c : ℂ) + (t : ℂ) * Complex.I) * K t) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun n _ => ‖LSeries.term a (c : ℂ) n‖ * M) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact ((LSeries.continuous_term_vertical a c n).mul hK).aestronglyMeasurable
  · intro n
    filter_upwards with t _
    rw [norm_mul, LSeries.norm_term_vertical]
    exact mul_le_mul_of_nonneg_left (hKB t) (norm_nonneg _)
  · filter_upwards with t _
    exact (summable_norm_iff.mpr h).mul_right _
  · exact intervalIntegrable_const
  · filter_upwards with t _
    exact (h.of_re_le_re (by simp) : LSeriesSummable _ ((c : ℂ) + (t : ℂ) *
        Complex.I)).LSeriesHasSum.mul_right (K t)

open Complex in
private lemma norm_exp_mul_I_mul (b t : ℝ) : ‖Complex.exp ((b : ℂ) * I * t)‖ = 1 := by
  rw [Complex.norm_exp]; simp

open Complex in
private lemma integral_exp_mul_I_mul {b : ℝ} (hb : b ≠ 0) (A B : ℝ) :
    ‖∫ t in A..B, Complex.exp ((b : ℂ) * I * t)‖ ≤ 2 / |b| := by
  have hc : (b : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hb) I_ne_zero
  rw [integral_exp_mul_complex hc, norm_div]
  have : ‖(b : ℂ) * I‖ = |b| := by simp
  rw [this]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_exp_mul_I_mul, norm_exp_mul_I_mul]; norm_num

private lemma integral_one_div_one_add_le_log (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, (1 + t)⁻¹ = Real.log (1 + T) := by
  have hd : ∀ x ∈ Set.uIcc 0 T, HasDerivAt (fun t => Real.log (1 + t)) (1 + x)⁻¹ x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have := ((hasDerivAt_id x).const_add 1).log (by simp; linarith [hx.1])
    simpa [one_div] using this
  have hc : ContinuousOn (fun t : ℝ => (1 + t)⁻¹) (Set.uIcc 0 T) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    rw [Set.uIcc_of_le hT] at hx; linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp

private lemma norm_intervalIntegral_le_of_norm_le_div {f : ℝ → ℂ} {K T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t, 0 ≤ t → ‖f t‖ ≤ K * (1 + t)⁻¹) :
    ‖∫ t in (0:ℝ)..T, f t‖ ≤ K * Real.log (1 + T) := by
  rw [← integral_one_div_one_add_le_log T hT, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall fun t ht => hb t ht.1.le) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
  rw [Set.uIcc_of_le hT] at hx; linarith [hx.1]

/-- Integral bound by the majorant `K / (1 + |t|)` on `[A, B]` with `A ≤ 0 ≤ B`. -/
private lemma norm_intervalIntegral_le_log {f : ℝ → ℂ} {K A B : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B)
    (hf : IntervalIntegrable f MeasureTheory.volume A B)
    (hb : ∀ t, ‖f t‖ ≤ K * (1 + |t|)⁻¹) :
    ‖∫ t in A..B, f t‖ ≤ K * (Real.log (1 + |A|) + Real.log (1 + B)) := by
  have h1 : ‖∫ t in (0:ℝ)..B, f t‖ ≤ K * Real.log (1 + B) :=
    norm_intervalIntegral_le_of_norm_le_div hB fun t ht => by have := hb t; rwa [abs_of_nonneg ht]
        at this
  have h2 : ‖∫ t in A..0, f t‖ ≤ K * Real.log (1 + |A|) := by
    have e : (∫ t in A..0, f t) = ∫ t in (0:ℝ)..(-A), f (-t) := by
      rw [intervalIntegral.integral_comp_neg]; simp
    rw [e, abs_of_nonpos hA]
    exact norm_intervalIntegral_le_of_norm_le_div (by linarith) fun t ht => by
      have := hb (-t); rwa [abs_neg, abs_of_nonneg ht] at this
  have m0 : (0:ℝ) ∈ Set.uIcc A B := by rw [Set.mem_uIcc]; left; exact ⟨hA, hB⟩
  have i1 : IntervalIntegrable f MeasureTheory.volume A 0 :=
    hf.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc m0)
  have i2 : IntervalIntegrable f MeasureTheory.volume 0 B :=
    hf.mono_set (Set.uIcc_subset_uIcc m0 Set.right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  refine (norm_add_le _ _).trans ?_
  linarith

open Complex in
/-- Bounds for `w(t) = α (3/2 + i t) + r`. -/
private lemma gamma_argument_bounds (α : ℝ) (hα : 0 < α) (r : ℂ) (hr : 0 ≤ r.re) :
    ∃ Kl Ku : ℝ, 0 < Kl ∧ 0 < Ku ∧ ∀ t : ℝ,
      3 * α / 2 ≤ ‖(α : ℂ) * ((3 / 2 : ℂ) + t * I) + r‖ ∧
      ‖((α : ℂ) * ((3 / 2 : ℂ) + t * I) + r)⁻¹‖ ≤ Kl * (1 + |t|)⁻¹ ∧
      ‖(α : ℂ) * ((3 / 2 : ℂ) + t * I) + r‖ ≤ Ku * (1 + |t|) := by
  set b := r.im with hb
  refine ⟨2 / (3 * α) * (1 + |b| / α) + 1 / α, 3 * α / 2 + |r.re| + α + |b|,
    by positivity, by positivity, fun t => ?_⟩
  set w : ℂ := (α : ℂ) * ((3 / 2 : ℂ) + t * I) + r with hw
  have hwre : w.re = 3 * α / 2 + r.re := by simp [w]; ring
  have hwim : w.im = α * t + b := by simp [w, b]
  have h1 : 3 * α / 2 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hwre, abs_of_nonneg (by linarith)] at this
    linarith
  have h2 : |α * t + b| ≤ ‖w‖ := by rw [← hwim]; exact Complex.abs_im_le_norm w
  have hw0 : 0 < ‖w‖ := by linarith
  refine ⟨h1, ?_, ?_⟩
  · rw [norm_inv]
    have hat : α * |t| ≤ |α * t + b| + |b| := by
      have := abs_add_le (α * t + b) (-b)
      rw [abs_neg, add_neg_cancel_right, abs_mul, abs_of_pos hα] at this
      exact this
    have key : 1 + |t| ≤ (2 / (3 * α) * (1 + |b| / α) + 1 / α) * ‖w‖ := by
      have e1 : |t| ≤ ‖w‖ / α + |b| / α := by
        rw [← add_div, le_div_iff₀ hα]; nlinarith
      have e2 : 1 ≤ 2 / (3 * α) * ‖w‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
      have e3 : |b| / α ≤ 2 / (3 * α) * ‖w‖ * (|b| / α) := by
        have : 0 ≤ |b| / α := by positivity
        nlinarith
      have e4 : (2 / (3 * α) * (1 + |b| / α) + 1 / α) * ‖w‖ =
          2 / (3 * α) * ‖w‖ + 2 / (3 * α) * ‖w‖ * (|b| / α) + ‖w‖ / α := by
        field_simp
      rw [e4]; linarith
    rw [inv_le_iff_one_le_mul₀ hw0]
    have hp : 0 < 1 + |t| := by positivity
    calc (1 : ℝ) = (1 + |t|) * (1 + |t|)⁻¹ := by field_simp
      _ ≤ (2 / (3 * α) * (1 + |b| / α) + 1 / α) * ‖w‖ * (1 + |t|)⁻¹ := by
          gcongr
      _ = _ := by ring
  · have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim] at this
    have h3 : |3 * α / 2 + r.re| ≤ 3 * α / 2 + |r.re| := by
      rw [abs_le]; constructor <;> linarith [abs_nonneg r.re, le_abs_self r.re, neg_abs_le r.re]
    have h4 : |α * t + b| ≤ α * |t| + |b| := by
      have := abs_add_le (α * t) b
      rwa [abs_mul, abs_of_pos hα] at this
    have h5 : 0 ≤ |t| := abs_nonneg t
    nlinarith [abs_nonneg b, abs_nonneg r.re]

open Complex in
/-- **The gamma-factor oscillatory integral.** For `log 2 ≤ |λ|` and `A ≤ 0 ≤ B`,
`∫_A^B e^{iλt} ψ(α (3/2 + it) + r) dt = O(1 + log (1 + |A|) + log (1 + B))`, uniformly. -/
private lemma norm_integral_exp_mul_digamma_le (α : ℝ) (hα : 0 < α) (r : ℂ) (hr : 0 ≤ r.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, Real.log 2 ≤ |lam| → ∀ A B : ℝ, A ≤ 0 → 0 ≤ B →
      ‖∫ t in A..B, Complex.exp ((lam : ℂ) * I * t) *
          Complex.digamma ((α : ℂ) * ((3 / 2 : ℂ) + t * I) + r)‖ ≤
        K * (1 + Real.log (1 + |A|) + Real.log (1 + B)) := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  obtain ⟨Kl, Ku, hKl, hKu, hw⟩ := gamma_argument_bounds α hα r hr
  set L0 : ℝ := |Real.log (3 * α / 2)| + |Real.log Ku| with hL0
  have hL00 : 0 ≤ L0 := by positivity
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨|Cd| * Kl + 2 * (2 * (L0 + Real.pi) + 1 + α * Kl), by positivity,
    fun lam hlam A B hA hB => ?_⟩
  have hlam0 : 0 < |lam| := by linarith
  have hlamne : lam ≠ 0 := abs_pos.mp hlam0
  have hinv : 1 / |lam| ≤ 2 := by
    rw [div_le_iff₀ hlam0]; linarith
  set w : ℝ → ℂ := fun t => (α : ℂ) * ((3 / 2 : ℂ) + t * I) + r with hwdef
  have hwre : ∀ t, (w t).re = 3 * α / 2 + r.re := fun t => by simp [w]; ring
  have hwslit : ∀ t, w t ∈ slitPlane := fun t => Or.inl (by rw [hwre]; positivity)
  have hw0 : ∀ t, w t ≠ 0 := fun t => slitPlane_ne_zero (hwslit t)
  have hwc : Continuous w := by simp only [w]; fun_prop
  have hwd : ∀ t : ℝ, HasDerivAt w ((α : ℂ) * I) t := by
    intro t
    have := ((((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (3 / 2 : ℂ)).const_mul
      (α : ℂ)
    refine (this.add_const r).congr_deriv ?_
    simp
  set e : ℝ → ℂ := fun t => Complex.exp ((lam : ℂ) * I * t) with he
  have hec : Continuous e := by simp only [e]; fun_prop
  have hen : ∀ t, ‖e t‖ = 1 := fun t => norm_exp_mul_I_mul lam t
  set E : ℝ → ℂ := fun t => Complex.digamma (w t) - Complex.log (w t) with hE
  have hψc : Continuous fun t => Complex.digamma (w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_digamma_of_re_pos (by rw [hwre]; positivity)).comp hwc.continuousAt
  have hlogc : Continuous fun t => Complex.log (w t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := w) (continuousAt_clog (hwslit t)) hwc.continuousAt
  have hEc : Continuous E := hψc.sub hlogc
  have hEb : ∀ t, ‖E t‖ ≤ (|Cd| * Kl) * (1 + |t|)⁻¹ := by
    intro t
    have harg : |Complex.arg (w t)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hwre]; positivity))
    have h := hCd (w t) (hw0 t) (by linarith [(abs_lt.mp harg).1])
      (by linarith [(abs_lt.mp harg).2])
    obtain ⟨-, hinvw, -⟩ := hw t
    rw [norm_inv] at hinvw
    calc ‖E t‖ ≤ Cd / ‖w t‖ := h
      _ ≤ |Cd| / ‖w t‖ := by gcongr; exact le_abs_self _
      _ = |Cd| * ‖w t‖⁻¹ := by ring
      _ ≤ |Cd| * (Kl * (1 + |t|)⁻¹) := by gcongr
      _ = _ := by ring
  have hsplit : (fun t => e t * Complex.digamma (w t)) =
      fun t => e t * E t + e t * Complex.log (w t) := by
    funext t; simp only [E]; ring
  change ‖∫ t in A..B, e t * Complex.digamma (w t)‖ ≤ _
  have i1 : IntervalIntegrable (fun t => e t * E t) MeasureTheory.volume A B :=
    (hec.mul hEc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => e t * Complex.log (w t)) MeasureTheory.volume A B :=
    (hec.mul hlogc).intervalIntegrable _ _
  rw [hsplit, intervalIntegral.integral_add i1 i2]
  have b1 : ‖∫ t in A..B, e t * E t‖ ≤ (|Cd| * Kl) * (Real.log (1 + |A|) + Real.log (1 + B)) :=
    norm_intervalIntegral_le_log hA hB ((hec.mul hEc).intervalIntegrable _ _) fun t => by
      rw [norm_mul, hen, one_mul]; exact hEb t
  -- integration by parts for the log term
  set c : ℂ := (lam : ℂ) * I with hc_def
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hlamne) I_ne_zero
  have hcn : ‖c‖ = |lam| := by simp [c]
  have hu : ∀ t ∈ Set.uIcc A B, HasDerivAt (fun t => Complex.log (w t)) (((α : ℂ) * I) / w t) t :=
    fun t _ => (hwd t).clog_real (hwslit t)
  have hv : ∀ t ∈ Set.uIcc A B, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
      (Complex.exp (c * t)) t := by
    intro t _
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * t)) hc]
    apply ((Complex.hasDerivAt_exp _).comp t _).div_const c
    simpa only [mul_one] using! ((hasDerivAt_id (t : ℂ)).const_mul _).comp_ofReal
  have hu'c : Continuous fun t => ((α : ℂ) * I) / w t := continuous_const.div hwc hw0
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hu'c.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (c * t)).intervalIntegrable _ _)
  have hcomm : (∫ t in A..B, e t * Complex.log (w t)) =
      ∫ t in A..B, Complex.log (w t) * Complex.exp (c * t) := by
    congr 1; funext t; simp only [e, c]; ring
  rw [hcomm, hibp]
  have hlog : ∀ t, ‖Complex.log (w t)‖ ≤ L0 + Real.log (1 + |t|) + Real.pi := by
    intro t
    obtain ⟨h1, -, h3⟩ := hw t
    have hw1 : 0 < ‖w t‖ := by linarith [show 0 < 3 * α / 2 by positivity]
    have hlogabs : |Real.log ‖w t‖| ≤ L0 + Real.log (1 + |t|) := by
      have hup : Real.log ‖w t‖ ≤ Real.log Ku + Real.log (1 + |t|) := by
        rw [← Real.log_mul hKu.ne' (by positivity)]
        exact Real.log_le_log hw1 h3
      have hlo : Real.log (3 * α / 2) ≤ Real.log ‖w t‖ := Real.log_le_log (by positivity) h1
      have hl1 : 0 ≤ Real.log (1 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log (3 * α / 2)), abs_nonneg (Real.log Ku)]
      · linarith [le_abs_self (Real.log Ku), abs_nonneg (Real.log (3 * α / 2))]
    calc ‖Complex.log (w t)‖ ≤ |(Complex.log (w t)).re| + |(Complex.log (w t)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ _ := by
        rw [Complex.log_re, Complex.log_im]
        exact add_le_add hlogabs (Complex.abs_arg_le_pi _)
  have hvn : ∀ t : ℝ, ‖Complex.exp (c * t) / c‖ = 1 / |lam| := by
    intro t; rw [norm_div, hcn, hc_def, norm_exp_mul_I_mul]
  have hint : ‖∫ t in A..B, ((α : ℂ) * I) / w t * (Complex.exp (c * t) / c)‖
      ≤ (α * Kl / |lam|) * (Real.log (1 + |A|) + Real.log (1 + B)) := by
    apply norm_intervalIntegral_le_log hA hB
    · exact (hu'c.mul (by fun_prop)).intervalIntegrable _ _
    intro t
    obtain ⟨-, hinvw, -⟩ := hw t
    rw [norm_inv] at hinvw
    rw [norm_mul, hvn, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hα]
    calc α / ‖w t‖ * (1 / |lam|) = α * ‖w t‖⁻¹ * (1 / |lam|) := by ring
      _ ≤ α * (Kl * (1 + |t|)⁻¹) * (1 / |lam|) := by gcongr
      _ = _ := by ring
  have hlA := hlog A
  have hlB := hlog B
  have hl1 : 0 ≤ Real.log (1 + |A|) := Real.log_nonneg (by linarith [abs_nonneg A])
  have hl2' : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hB] at hlB
  have hb2 : ‖Complex.log (w B) * (Complex.exp (c * B) / c) -
      Complex.log (w A) * (Complex.exp (c * A) / c) -
      ∫ t in A..B, ((α : ℂ) * I) / w t * (Complex.exp (c * t) / c)‖ ≤
      (L0 + Real.log (1 + B) + Real.pi) * (1 / |lam|) +
        (L0 + Real.log (1 + |A|) + Real.pi) * (1 / |lam|) +
        (α * Kl / |lam|) * (Real.log (1 + |A|) + Real.log (1 + B)) := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul, hvn, hvn]
      gcongr
  have hb3 : (L0 + Real.log (1 + B) + Real.pi) * (1 / |lam|) +
        (L0 + Real.log (1 + |A|) + Real.pi) * (1 / |lam|) +
        (α * Kl / |lam|) * (Real.log (1 + |A|) + Real.log (1 + B)) ≤
      2 * (2 * (L0 + Real.pi) + 1 + α * Kl) * (1 + Real.log (1 + |A|) + Real.log (1 + B)) := by
    have e : (α * Kl / |lam|) = α * Kl * (1 / |lam|) := by ring
    rw [e]
    have hpos : 0 ≤ 1 / |lam| := by positivity
    have hX : 0 ≤ Real.log (1 + |A|) + Real.log (1 + B) := by linarith
    have hαK : 0 ≤ α * Kl := by positivity
    have hp : 0 ≤ Real.pi := Real.pi_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hinv (by positivity : (0:ℝ) ≤ L0 + Real.pi),
      mul_le_mul_of_nonneg_left hinv hl1, mul_le_mul_of_nonneg_left hinv hl2',
      mul_le_mul_of_nonneg_left hinv (mul_nonneg hαK hX), mul_nonneg hL00 hX,
      mul_nonneg hp hX, mul_nonneg hαK hX]
  calc _ ≤ ‖∫ t in A..B, e t * E t‖ + ‖Complex.log (w B) * (Complex.exp (c * B) / c) -
        Complex.log (w A) * (Complex.exp (c * A) / c) -
        ∫ t in A..B, ((α : ℂ) * I) / w t * (Complex.exp (c * t) / c)‖ := norm_add_le _ _
    _ ≤ (|Cd| * Kl) * (Real.log (1 + |A|) + Real.log (1 + B)) +
        2 * (2 * (L0 + Real.pi) + 1 + α * Kl) * (1 + Real.log (1 + |A|) + Real.log (1 + B)) :=
        add_le_add b1 (hb2.trans hb3)
    _ ≤ _ := by
        have h0 : 0 ≤ |Cd| * Kl := by positivity
        nlinarith

open Complex in
/-- **The archimedean part on `Re s = 3/2`.** -/
private lemma norm_integral_exp_mul_archimedean_le (m : ℕ) (Q : ℝ) {d : ℕ} (α : Fin d → ℝ) (r : Fin
    d → ℂ)
    (hα : ∀ i, 0 < α i) (hr : ∀ i, 0 ≤ (r i).re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lam : ℝ, Real.log 2 ≤ |lam| → ∀ A B : ℝ, A ≤ 0 → 0 ≤ B →
      ‖∫ t in A..B, Complex.exp ((lam : ℂ) * I * t) *
          ((m : ℂ) / (((3 / 2 : ℝ) : ℂ) + t * I) + Complex.log Q +
            (∑ i, (α i : ℂ) * digamma (α i * (((3 / 2 : ℝ) : ℂ) + t * I) + r i)) +
            (m : ℂ) / (((3 / 2 : ℝ) : ℂ) + t * I - 1))‖ ≤
        K * (1 + Real.log (1 + |A|) + Real.log (1 + B)) := by
  have hψ := fun i => norm_integral_exp_mul_digamma_le (α i) (hα i) (r i) (hr i)
  choose Kψ hKψ0 hKψ using hψ
  refine ⟨8 * m + 4 * ‖Complex.log Q‖ + ∑ i, α i * Kψ i, by
    have : 0 ≤ ∑ i, α i * Kψ i := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (hKψ0 i)
    positivity, fun lam hlam A B hA hB => ?_⟩
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlam0 : 0 < |lam| := by linarith
  have hlamne : lam ≠ 0 := abs_pos.mp hlam0
  set s : ℝ → ℂ := fun t => ((3 / 2 : ℝ) : ℂ) + t * I with hs
  have hsc : Continuous s := by simp only [s]; fun_prop
  have hsre : ∀ t, (s t).re = 3 / 2 := fun t => by simp [s]
  have hs0 : ∀ t, s t ≠ 0 := fun t h => by have := hsre t; rw [h] at this; norm_num at this
  have hs10 : ∀ t, s t - 1 ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp [s] at this; norm_num at this
  have hsinv : ∀ t, ‖(s t)⁻¹‖ ≤ 4 * (1 + |t|)⁻¹ := by
    intro t
    have h1 : 3 / 2 ≤ ‖s t‖ := by
      have := Complex.abs_re_le_norm (s t); rw [hsre] at this; norm_num at this; linarith
    have h2 : |t| ≤ ‖s t‖ := by
      have := Complex.abs_im_le_norm (s t); simpa [s] using this
    rw [norm_inv, inv_le_iff_one_le_mul₀ (by linarith)]
    have hp : 0 < 1 + |t| := by positivity
    rw [show 4 * (1 + |t|)⁻¹ * ‖s t‖ = 4 * ‖s t‖ / (1 + |t|) by field_simp]
    rw [le_div_iff₀ hp]; linarith
  have hs1inv : ∀ t, ‖(s t - 1)⁻¹‖ ≤ 4 * (1 + |t|)⁻¹ := by
    intro t
    have h1 : 1 / 2 ≤ ‖s t - 1‖ := by
      have := Complex.abs_re_le_norm (s t - 1)
      have hre : (s t - 1).re = 1 / 2 := by simp [s]; norm_num
      rw [hre, abs_of_pos (by norm_num)] at this; exact this
    have h2 : |t| ≤ ‖s t - 1‖ := by
      have := Complex.abs_im_le_norm (s t - 1); simpa [s] using this
    rw [norm_inv, inv_le_iff_one_le_mul₀ (by linarith)]
    have hp : 0 < 1 + |t| := by positivity
    rw [show 4 * (1 + |t|)⁻¹ * ‖s t - 1‖ = 4 * ‖s t - 1‖ / (1 + |t|) by field_simp]
    rw [le_div_iff₀ hp]; linarith
  set e : ℝ → ℂ := fun t => Complex.exp ((lam : ℂ) * I * t) with he
  have hec : Continuous e := by simp only [e]; fun_prop
  have hen : ∀ t, ‖e t‖ = 1 := fun t => norm_exp_mul_I_mul lam t
  have hargre : ∀ i t, 0 < ((α i : ℂ) * s t + r i).re := fun i t => by
    simp only [Complex.add_re, Complex.re_ofReal_mul, hsre]
    have := hα i; have := hr i; positivity
  have hψc : ∀ i, Continuous fun t => Complex.digamma ((α i : ℂ) * s t + r i) := fun i =>
    continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_digamma_of_re_pos (hargre i t)).comp (f := fun t => (α i : ℂ) * s t + r i)
        (by fun_prop)
  have hpt : ∀ t, e t * ((m : ℂ) / s t + Complex.log Q +
      (∑ i, (α i : ℂ) * digamma (α i * s t + r i)) + (m : ℂ) / (s t - 1)) =
      (m : ℂ) * (e t * (s t)⁻¹) + Complex.log Q * e t +
        ∑ i, (α i : ℂ) * (e t * digamma (α i * s t + r i)) + (m : ℂ) * (e t * (s t - 1)⁻¹) := by
    intro t
    have hσ : e t * ∑ i, (α i : ℂ) * digamma (α i * s t + r i) =
        ∑ i, (α i : ℂ) * (e t * digamma (α i * s t + r i)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [mul_add, mul_add, mul_add, hσ]
    simp only [div_eq_mul_inv]
    ring
  change ‖∫ t in A..B, e t * ((m : ℂ) / s t + Complex.log Q +
      (∑ i, (α i : ℂ) * digamma (α i * s t + r i)) + (m : ℂ) / (s t - 1))‖ ≤ _
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun t => (m : ℂ) * (e t * (s t)⁻¹)) MeasureTheory.volume A B :=
    (continuous_const.mul (hec.mul (hsc.inv₀ hs0))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => Complex.log Q * e t) MeasureTheory.volume A B :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t => ∑ i, (α i : ℂ) * (e t * digamma (α i * s t + r i)))
      MeasureTheory.volume A B :=
    (continuous_finsetSum _ fun i _ => continuous_const.mul (hec.mul (hψc i))).intervalIntegrable _
        _
  have i4 : IntervalIntegrable (fun t => (m : ℂ) * (e t * (s t - 1)⁻¹)) MeasureTheory.volume A B :=
    (continuous_const.mul (hec.mul ((hsc.sub continuous_const).inv₀ hs10))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((i1.add i2).add i3) i4,
    intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_finsetSum
      (f := fun i t => (α i : ℂ) * (e t * digamma ((α i : ℂ) * s t + r i))) (fun i _ =>
      (continuous_const.mul (hec.mul (hψc i))).intervalIntegrable A B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const_mul]
  set X : ℝ := 1 + Real.log (1 + |A|) + Real.log (1 + B) with hX
  have hl1 : 0 ≤ Real.log (1 + |A|) := Real.log_nonneg (by linarith [abs_nonneg A])
  have hl2' : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have b1 : ‖(m : ℂ) * ∫ t in A..B, e t * (s t)⁻¹‖ ≤ 4 * m * X := by
    rw [norm_mul, Complex.norm_natCast]
    have := norm_intervalIntegral_le_log (f := fun t => e t * (s t)⁻¹) hA hB
      ((hec.mul (hsc.inv₀ hs0)).intervalIntegrable _ _)
      (K := 4) fun t => by rw [norm_mul, hen, one_mul]; exact hsinv t
    calc (m : ℝ) * ‖∫ t in A..B, e t * (s t)⁻¹‖ ≤ m * (4 * (Real.log (1 + |A|) + Real.log (1 + B)))
        := by
          gcongr
      _ ≤ 4 * m * X := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have b4 : ‖(m : ℂ) * ∫ t in A..B, e t * (s t - 1)⁻¹‖ ≤ 4 * m * X := by
    rw [norm_mul, Complex.norm_natCast]
    have := norm_intervalIntegral_le_log (f := fun t => e t * (s t - 1)⁻¹) hA hB
      ((hec.mul ((hsc.sub continuous_const).inv₀ hs10)).intervalIntegrable _ _)
      (K := 4) fun t => by rw [norm_mul, hen, one_mul]; exact hs1inv t
    calc (m : ℝ) * ‖∫ t in A..B, e t * (s t - 1)⁻¹‖ ≤ m * (4 * (Real.log (1 + |A|) + Real.log (1 +
        B))) := by
          gcongr
      _ ≤ 4 * m * X := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have b2 : ‖Complex.log Q * ∫ t in A..B, e t‖ ≤ 4 * ‖Complex.log Q‖ * X := by
    rw [norm_mul]
    have h := integral_exp_mul_I_mul hlamne A B
    have h2 : 2 / |lam| ≤ 4 := by rw [div_le_iff₀ hlam0]; linarith
    calc ‖Complex.log Q‖ * ‖∫ t in A..B, e t‖ ≤ ‖Complex.log Q‖ * 4 := by
          gcongr; exact h.trans h2
      _ ≤ 4 * ‖Complex.log Q‖ * X := by nlinarith [norm_nonneg (Complex.log Q)]
  have b3 : ‖∑ i, (α i : ℂ) * ∫ t in A..B, e t * digamma (α i * s t + r i)‖ ≤
      (∑ i, α i * Kψ i) * X := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hα i), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hα i).le
    have := hKψ i lam hlam A B hA hB
    simpa [s] using this
  calc _ ≤ ‖(m : ℂ) * ∫ t in A..B, e t * (s t)⁻¹‖ + ‖Complex.log Q * ∫ t in A..B, e t‖ +
        ‖∑ i, (α i : ℂ) * ∫ t in A..B, e t * digamma (α i * s t + r i)‖ +
        ‖(m : ℂ) * ∫ t in A..B, e t * (s t - 1)⁻¹‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_add_le _ _
    _ ≤ 4 * m * X + 4 * ‖Complex.log Q‖ * X + (∑ i, α i * Kψ i) * X + 4 * m * X := by gcongr
    _ = _ := by ring

/-- `∑_{k < 2n, k ≠ n} 1/|n - k| ≤ 2 (1 + log n)`. -/
private lemma sum_inv_abs_sub_le (n : ℕ) :
    ∑ k ∈ (Finset.range (2 * n)).erase n, (1 : ℝ) / |(n : ℝ) - k| ≤ 2 * (1 + Real.log n) := by
  have hH : (∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1)) ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    have e : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
      rw [harmonic]; push_cast; simp [one_div]
    rw [← e]; exact h
  have hsplit : (Finset.range (2 * n)).erase n = Finset.range n ∪ Finset.Ico (n + 1) (2 * n) := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range n) (Finset.Ico (n + 1) (2 * n)) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have h1 : ∑ k ∈ Finset.range n, (1 : ℝ) / |(n : ℝ) - k| =
      ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have : ((n - 1 - j : ℕ) : ℝ) = (n : ℝ) - 1 - j := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this, show (n : ℝ) - ((n : ℝ) - 1 - j) = (j : ℝ) + 1 by ring,
      abs_of_pos (by positivity)]
  have h2 : ∑ k ∈ Finset.Ico (n + 1) (2 * n), (1 : ℝ) / |(n : ℝ) - k| ≤
      ∑ j ∈ Finset.range n, (1 : ℝ) / ((j : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hsub : Finset.range (2 * n - (n + 1)) ⊆ Finset.range n := by
      intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity)
    push_cast
    rw [show (n : ℝ) - ((n : ℝ) + 1 + j) = -((j : ℝ) + 1) by ring, abs_neg,
      abs_of_pos (by positivity)]
  rw [h1]; linarith

/-- **The near-diagonal sum.** For `‖Λ k‖ ≤ C₁ k^θ₁` with `θ₁ < 1/2`, a summable majorant `g n`
of `k ↦ C₁ k^(θ₁ - 3/2) / |log n - log k|` (`k ≠ n`) with sum bounded independently of `n`. -/
private lemma exists_near_diagonal_bound (θ₁ C₁ : ℝ) (hθ : θ₁ < 1 / 2) (hC₁ : 0 ≤ C₁) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n → ∃ g : ℕ → ℝ, (∀ k, 0 ≤ g k) ∧ Summable g ∧
      ∑' k, g k ≤ K ∧ ∀ k : ℕ, 1 ≤ k → k ≠ n →
        C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / |Real.log n - Real.log k| ≤ g k := by
  classical
  have hp : θ₁ - 3 / 2 < -1 := by linarith
  have hsum := Real.summable_nat_rpow.2 hp
  set Z0 : ℝ := ∑' k : ℕ, (k : ℝ) ^ (θ₁ - 3 / 2) with hZ0
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := 1 / 2 - θ₁ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set Kn : ℝ := C₁ * 2 ^ (3 / 2 - θ₁) * 4 * (1 + 1 / δ) with hKn
  have hZ00 : 0 ≤ Z0 := tsum_nonneg fun k => by positivity
  refine ⟨C₁ / Real.log 2 * Z0 + Kn, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set S : Finset ℕ := ((Finset.range (2 * n)).erase n).filter (fun k => n < 2 * k) with hS
  set g : ℕ → ℝ := fun k => C₁ / Real.log 2 * (k : ℝ) ^ (θ₁ - 3 / 2) +
    (if k ∈ S then C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) / |(n : ℝ) - k| else 0) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [g]; split_ifs <;> positivity
  have hfin : Summable fun k => (if k ∈ S then C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) /
      |(n : ℝ) - k| else 0) :=
    summable_of_ne_finset_zero (s := S) fun k hk => ite_eq_right hk
  have hgs : Summable g := (hsum.mul_left _).add hfin
  refine ⟨g, hg0, hgs, ?_, ?_⟩
  · change ∑' k : ℕ, (C₁ / Real.log 2 * (k : ℝ) ^ (θ₁ - 3 / 2) +
      (if k ∈ S then C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) / |(n : ℝ) - k| else 0)) ≤ _
    rw [(hsum.mul_left _).tsum_add hfin]
    rw [tsum_mul_left, tsum_eq_sum (s := S) (f := fun k : ℕ => if k ∈ S then
      C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) / |(n : ℝ) - k| else 0) fun k hk => ite_eq_right
          hk]
    rw [Finset.sum_ite_of_true (fun k hk => hk)]
    gcongr
    -- the finite part
    have hb : ∀ k ∈ S, C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) / |(n : ℝ) - k| =
        C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) * (1 / |(n : ℝ) - k|) := fun k _ => by ring
    rw [Finset.sum_congr rfl hb, ← Finset.mul_sum]
    have hS' : ∑ k ∈ S, (1 : ℝ) / |(n : ℝ) - k| ≤ 2 * (1 + Real.log n) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => by positivity).trans (sum_inv_abs_sub_le n)
    have hpow : ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) = 2 ^ (3 / 2 - θ₁) * 2 * (n : ℝ) ^ (-δ) := by
      rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg hn0.le]
      have e1 : (n : ℝ) ^ (θ₁ - 3 / 2) = (n : ℝ) ^ (θ₁ - 1 / 2) * (n : ℝ)⁻¹ := by
        rw [show θ₁ - 3 / 2 = (θ₁ - 1 / 2) + (-1 : ℝ) by ring, Real.rpow_add hn0, Real.rpow_neg_one]
      have e2 : (2 : ℝ) ^ (θ₁ - 3 / 2) = ((2 : ℝ) ^ (3 / 2 - θ₁))⁻¹ := by
        rw [← Real.rpow_neg (by norm_num)]; ring_nf
      have e3 : (n : ℝ) ^ δ = ((n : ℝ) ^ (θ₁ - 1 / 2))⁻¹ := by
        rw [← Real.rpow_neg hn0.le]; rw [hδ]; ring_nf
      rw [e1, e2, e3, inv_inv]
      have h2 : (0:ℝ) < 2 ^ (3 / 2 - θ₁) := by positivity
      field_simp
    have hlogn : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hn0.le hδ0
    have hnδ : (n : ℝ) ^ (-δ) * (n : ℝ) ^ δ = 1 := by
      rw [← Real.rpow_add hn0]; simp
    have hnδ1 : (n : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    have hnδ0 : 0 ≤ (n : ℝ) ^ (-δ) := by positivity
    calc C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) * ∑ k ∈ S, (1 : ℝ) / |(n : ℝ) - k|
        ≤ C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) * (2 * (1 + Real.log n)) := by
          gcongr
      _ = C₁ * 2 ^ (3 / 2 - θ₁) * 4 * ((n : ℝ) ^ (-δ) * (1 + Real.log n)) := by
          rw [mul_assoc C₁, hpow]; ring
      _ ≤ C₁ * 2 ^ (3 / 2 - θ₁) * 4 * (1 + 1 / δ) := by
          gcongr
          calc (n : ℝ) ^ (-δ) * (1 + Real.log n) ≤ (n : ℝ) ^ (-δ) * (1 + (n : ℝ) ^ δ / δ) := by
                gcongr
            _ = (n : ℝ) ^ (-δ) + ((n : ℝ) ^ (-δ) * (n : ℝ) ^ δ) / δ := by ring
            _ ≤ 1 + 1 / δ := by rw [hnδ]; linarith
  · intro k hk hkn
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hpow0 : 0 ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) := by positivity
    have hfin0 : 0 ≤ (if k ∈ S then C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) /
        |(n : ℝ) - k| else 0) := by split_ifs <;> positivity
    by_cases hfar : 2 * k ≤ n ∨ 2 * n ≤ k
    · -- far: `|log n - log k| ≥ log 2`
      have hlog : Real.log 2 ≤ |Real.log n - Real.log k| := by
        rcases hfar with h | h
        · have h' : (2 : ℝ) * k ≤ n := by exact_mod_cast h
          rw [abs_of_nonneg (by
            have := Real.log_le_log hk0 (by linarith : (k : ℝ) ≤ n); linarith)]
          rw [← Real.log_div hn0.ne' hk0.ne']
          exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hk0]; linarith)
        · have h' : (2 : ℝ) * n ≤ k := by exact_mod_cast h
          rw [abs_sub_comm, abs_of_nonneg (by
            have := Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ k); linarith)]
          rw [← Real.log_div hk0.ne' hn0.ne']
          exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hn0]; linarith)
      calc C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / |Real.log n - Real.log k|
          ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / Real.log 2 :=
            div_le_div_of_nonneg_left hpow0 hl2 hlog
        _ = C₁ / Real.log 2 * (k : ℝ) ^ (θ₁ - 3 / 2) := by ring
        _ ≤ g k := by simp only [g]; linarith
    · push Not at hfar
      have hkS : k ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
        omega
      have hnk : (n : ℝ) ≠ k := by exact_mod_cast (Ne.symm hkn)
      have hdist : 0 < |(n : ℝ) - k| := abs_pos.2 (sub_ne_zero.2 hnk)
      have h2k : (n : ℝ) < 2 * k := by exact_mod_cast hfar.1
      have hk2 : (k : ℝ) < 2 * n := by exact_mod_cast hfar.2
      -- `|log n - log k| ≥ |n - k| / (2 n)`
      have hlog : |(n : ℝ) - k| / (2 * n) ≤ |Real.log n - Real.log k| := by
        rcases lt_or_gt_of_ne hnk with h | h
        · -- n < k
          have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hk0 hn0)
          rw [Real.log_div hk0.ne' hn0.ne', inv_div] at h1
          have hlk : Real.log n ≤ Real.log k := Real.log_le_log hn0 h.le
          rw [abs_of_neg (by linarith : (n : ℝ) - k < 0),
            abs_of_nonpos (by linarith : Real.log n - Real.log k ≤ 0)]
          have h3 : ((k : ℝ) - n) / (2 * n) ≤ 1 - (n : ℝ) / k := by
            rw [div_le_iff₀ (by positivity)]
            have e : (1 - (n : ℝ) / k) * (2 * n) = 2 * n * (k - n) / k := by field_simp
            rw [e, le_div_iff₀ hk0]; nlinarith
          have e2 : -((n : ℝ) - k) / (2 * n) = ((k : ℝ) - n) / (2 * n) := by ring
          rw [e2]
          linarith
        · -- k < n
          have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hn0 hk0)
          rw [Real.log_div hn0.ne' hk0.ne', inv_div] at h1
          have hlk : Real.log k ≤ Real.log n := Real.log_le_log hk0 h.le
          rw [abs_of_pos (by linarith : (0 : ℝ) < n - k),
            abs_of_nonneg (by linarith : 0 ≤ Real.log n - Real.log k)]
          have h3 : ((n : ℝ) - k) / (2 * n) ≤ 1 - (k : ℝ) / n := by
            rw [div_le_iff₀ (by positivity)]
            have e : (1 - (k : ℝ) / n) * (2 * n) = 2 * (n - k) := by field_simp
            rw [e]; nlinarith
          linarith
      have hkpow : (k : ℝ) ^ (θ₁ - 3 / 2) ≤ ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have hlogpos : 0 < |(n : ℝ) - k| / (2 * n) := by positivity
      calc C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / |Real.log n - Real.log k|
          ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / (|(n : ℝ) - k| / (2 * n)) :=
            div_le_div_of_nonneg_left hpow0 hlogpos hlog
        _ ≤ C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) / (|(n : ℝ) - k| / (2 * n)) := by gcongr
        _ = C₁ * ((n : ℝ) / 2) ^ (θ₁ - 3 / 2) * (2 * n) / |(n : ℝ) - k| := by
            field_simp
        _ ≤ g k := by
            simp only [g, ite_eq_left hkS]
            have : 0 ≤ C₁ / Real.log 2 * (k : ℝ) ^ (θ₁ - 3 / 2) := by positivity
            linarith

open Complex in
/-- The Dirichlet-series term on `Re s = 3/2` against `e^{iλt}`. -/
private lemma term_mul_exp_line_three_halves (Λ : ℕ → ℂ) (lam t : ℝ) {k : ℕ} (hk : k ≠ 0) :
    LSeries.term Λ (((3 / 2 : ℝ) : ℂ) + t * I) k * Complex.exp ((lam : ℂ) * I * t) =
      Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((lam - Real.log k : ℝ) : ℂ) * I * t) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [LSeries.term_of_ne_zero hk, show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast,
    ofReal_cpow_eq_exp hk0, Real.rpow_def_of_pos hk0, Complex.ofReal_exp, div_eq_mul_inv,
    ← Complex.exp_neg, mul_assoc, ← Complex.exp_add, mul_assoc (Λ k), ← Complex.exp_add]
  congr 2
  push_cast
  ring

open Complex in
/-- **The Dirichlet part on `Re s = 3/2`.** With `‖Λ k‖ ≤ C₁ k^θ₁`, `θ₁ < 1/2`: against
`n^{it}` the integral is `(B - A) Λ(n) n^{-3/2} + O(1)`, against `n^{-it}` it is `O(1)`,
uniformly in `n ≥ 2` and `A, B`. -/
private lemma integral_LSeries_line_three_halves_mul_exp (Λ : ℕ → ℂ) (θ₁ C₁ : ℝ) (hθ : θ₁ < 1 / 2)
    (hC₁ : 0 ≤ C₁)
    (hΛb : ∀ k : ℕ, k ≠ 0 → ‖Λ k‖ ≤ C₁ * (k : ℝ) ^ θ₁) :
    LSeriesSummable Λ ((3 / 2 : ℝ) : ℂ) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n → ∀ A B : ℝ,
      ‖(∫ t in A..B, LSeries Λ (((3 / 2 : ℝ) : ℂ) + t * I) *
          Complex.exp ((Real.log n : ℂ) * I * t)) -
        ((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ K ∧
      ‖∫ t in A..B, LSeries Λ (((3 / 2 : ℝ) : ℂ) + t * I) *
          Complex.exp (((-Real.log n : ℝ) : ℂ) * I * t)‖ ≤ K := by
  have hsum : LSeriesSummable Λ ((3 / 2 : ℝ) : ℂ) :=
    LSeriesSummable_of_le_const_mul_rpow (x := θ₁ + 1) (by simp; linarith)
      ⟨C₁, fun k hk => by convert hΛb k hk using 3; ring⟩
  refine ⟨hsum, ?_⟩
  obtain ⟨Kn, hKn0, hnear⟩ := exists_near_diagonal_bound θ₁ C₁ hθ hC₁
  have hp : θ₁ - 3 / 2 < -1 := by linarith
  have hpow_sum := (Real.summable_nat_rpow.2 hp).mul_left (C₁ * (2 / Real.log 2))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Z1 : ℝ := ∑' k : ℕ, C₁ * (2 / Real.log 2) * (k : ℝ) ^ (θ₁ - 3 / 2) with hZ1
  have hZ10 : 0 ≤ Z1 := tsum_nonneg fun k => by positivity
  refine ⟨2 * Kn + Z1, by positivity, fun n hn A B => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : n ≠ 0 := by omega
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  -- the norm of the coefficient
  have hcoef : ∀ k : ℕ, k ≠ 0 →
      ‖Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖Λ k‖ * (k : ℝ) ^ (-(3 / 2 : ℝ)) ≤ C₁ * (k : ℝ) ^ θ₁ * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
          gcongr; exact hΛb k hk
      _ = C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) := by
          rw [mul_assoc, ← Real.rpow_add hk0]; ring_nf
  have hint : ∀ (lam : ℝ) (k : ℕ), k ≠ 0 →
      (∫ t in A..B, LSeries.term Λ (((3 / 2 : ℝ) : ℂ) + t * I) k *
          Complex.exp ((lam : ℂ) * I * t)) =
        Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          ∫ t in A..B, Complex.exp (((lam - Real.log k : ℝ) : ℂ) * I * t) := by
    intro lam k hk
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => term_mul_exp_line_three_halves Λ lam t hk
  have hKb : ∀ lam : ℝ, ∀ t : ℝ, ‖Complex.exp ((lam : ℂ) * I * t)‖ ≤ 1 :=
    fun lam t => (norm_exp_mul_I_mul lam t).le
  constructor
  · obtain ⟨g, hg0, hgs, hgK, hgb⟩ := hnear n hn
    have hS := hasSum_intervalIntegral_term_mul hsum (K := fun t : ℝ => Complex.exp ((Real.log n :
        ℂ) * I * t))
      (by fun_prop) (hKb (Real.log n)) A B
    have hS' := hS.sub (hasSum_ite_eq n (((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ)
        : ℂ)))
    have hb : ∀ k : ℕ, ‖(∫ t in A..B, LSeries.term Λ (((3 / 2 : ℝ) : ℂ) + t * I) k *
        Complex.exp ((Real.log n : ℂ) * I * t)) -
        (if k = n then ((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) else 0)‖ ≤
        2 * g k := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp only [LSeries.term_zero, zero_mul, intervalIntegral.integral_zero,
          ite_eq_right (Ne.symm hn1), sub_zero, norm_zero]
        have := hg0 0; linarith
      rw [hint _ k hk0]
      by_cases hkn : k = n
      · subst hkn
        simp only [sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
          intervalIntegral.integral_const, Complex.real_smul, mul_one, ite_true]
        rw [show Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (((B - A : ℝ)) : ℂ) -
          ((B - A : ℝ) : ℂ) * Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) = 0 by ring, norm_zero]
        have := hg0 k; linarith
      · rw [ite_eq_right hkn, sub_zero, norm_mul]
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hβ : Real.log n - Real.log k ≠ 0 := by
          intro h
          have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
          have := Real.log_injOn_pos (Set.mem_Ioi.2 hn0) (Set.mem_Ioi.2 hk') (by linarith)
          exact hkn (by exact_mod_cast this.symm)
        have hJ := integral_exp_mul_I_mul hβ A B
        have hg := hgb k hk1 hkn
        have hpos : 0 < |Real.log n - Real.log k| := abs_pos.2 hβ
        calc ‖Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              ‖∫ t in A..B, Complex.exp (((Real.log n - Real.log k : ℝ) : ℂ) * I * t)‖
            ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) * (2 / |Real.log n - Real.log k|) := by
              gcongr
              exact hcoef k hk0
          _ = 2 * (C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) / |Real.log n - Real.log k|) := by ring
          _ ≤ 2 * g k := by gcongr
    have := hS'.norm_le_of_bounded (hgs.hasSum.mul_left 2) hb
    refine this.trans ?_
    have : 0 ≤ Z1 := hZ10
    linarith
  · have hS := hasSum_intervalIntegral_term_mul hsum
      (K := fun t : ℝ => Complex.exp (((-Real.log n : ℝ) : ℂ) * I * t))
      (by fun_prop) (hKb (-Real.log n)) A B
    have hb : ∀ k : ℕ, ‖∫ t in A..B, LSeries.term Λ (((3 / 2 : ℝ) : ℂ) + t * I) k *
        Complex.exp (((-Real.log n : ℝ) : ℂ) * I * t)‖ ≤
        C₁ * (2 / Real.log 2) * (k : ℝ) ^ (θ₁ - 3 / 2) := by
      intro k
      rcases eq_or_ne k 0 with rfl | hk0
      · simp only [LSeries.term_zero, zero_mul, intervalIntegral.integral_zero, norm_zero]
        positivity
      rw [hint _ k hk0, norm_mul]
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
      have hlk : 0 ≤ Real.log k := Real.log_nonneg hk1
      have hβ : -Real.log n - Real.log k ≠ 0 := by intro h; linarith
      have hJ := integral_exp_mul_I_mul hβ A B
      have hβa : Real.log 2 ≤ |-Real.log n - Real.log k| := by
        rw [abs_of_neg (by linarith)]; linarith
      have hJ' : 2 / |-Real.log n - Real.log k| ≤ 2 / Real.log 2 :=
        div_le_div_of_nonneg_left (by norm_num) hl2 hβa
      calc ‖Λ k * (((k : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ *
            ‖∫ t in A..B, Complex.exp (((-Real.log n - Real.log k : ℝ) : ℂ) * I * t)‖
          ≤ C₁ * (k : ℝ) ^ (θ₁ - 3 / 2) * (2 / Real.log 2) := by
            gcongr
            · exact hcoef k hk0
            · exact hJ.trans hJ'
        _ = C₁ * (2 / Real.log 2) * (k : ℝ) ^ (θ₁ - 3 / 2) := by ring
    have := hS.norm_le_of_bounded hpow_sum.hasSum hb
    refine this.trans ?_
    linarith

/-! ### The contour -/

open Complex Filter Topology Set in
/-- **The weighted argument principle** on the rectangle `[a, b] × [c, d]` for an entire `H`:
the boundary integral of `H'/H · x^s` is `2πi ∑_ρ ord_ρ(H) x^ρ` over the zeros inside. -/
private lemma boundaryIntegral_logDeriv_mul_cpow (H : ℂ → ℂ) (hH : Differentiable ℂ H) (x : ℝ) (hx
    : 0 < x)
    (a b c d : ℝ) (Z : Finset ℂ) (hZ : ∀ p ∈ Z, a < p.re ∧ p.re < b ∧ c < p.im ∧ p.im < d)
    (hZ2 : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → c ≤ s.im → s.im ≤ d → H s = 0 → s ∈ Z)
    (hfin : ∀ p, analyticOrderAt H p ≠ ⊤) (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ u : ℝ in a..b, deriv H ((u : ℂ) + (c : ℂ) * I) / H ((u : ℂ) + (c : ℂ) * I) *
        (x : ℂ) ^ ((u : ℂ) + (c : ℂ) * I))
      - (∫ u : ℝ in a..b, deriv H ((u : ℂ) + (d : ℂ) * I) / H ((u : ℂ) + (d : ℂ) * I) *
        (x : ℂ) ^ ((u : ℂ) + (d : ℂ) * I))
      + I • (∫ y : ℝ in c..d, deriv H ((b : ℂ) + (y : ℂ) * I) / H ((b : ℂ) + (y : ℂ) * I) *
        (x : ℂ) ^ ((b : ℂ) + (y : ℂ) * I))
      - I • (∫ y : ℝ in c..d, deriv H ((a : ℂ) + (y : ℂ) * I) / H ((a : ℂ) + (y : ℂ) * I) *
        (x : ℂ) ^ ((a : ℂ) + (y : ℂ) * I))
      = 2 * (Real.pi : ℂ) * I * ∑ p ∈ Z, (analyticOrderNatAt H p : ℂ) * (x : ℂ) ^ p := by
  classical
  set F : ℂ → ℂ := fun s => deriv H s / H s * (x : ℂ) ^ s with hF
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  let mo : ℂ → ℕ := fun p => analyticOrderNatAt H p
  let r : ℂ → ℂ := fun p => (mo p : ℂ) * (x : ℂ) ^ p
  have hcpowd : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) s :=
    fun s => differentiableAt_id.const_cpow (Or.inl hx0)
  have hloc : ∀ p ∈ Z, ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ p ∧
      ∀ᶠ s in 𝓝[≠] p, F s = r p / (s - p) + φ s := by
    intro p hp
    have hm : analyticOrderAt H p = (mo p : ℕ) := (ENat.natCast_toNat (hfin p)).symm
    obtain ⟨ξ₁, hξ₁a, hξ₁0, hξ₁e⟩ := (hH.analyticAt p).analyticOrderAt_eq_natCast.mp hm
    have hξloc : ∀ᶠ s in 𝓝[≠] p, H s = (s - p) ^ ((mo p : ℕ) : ℤ) * ξ₁ s := by
      filter_upwards [nhdsWithin_le_nhds hξ₁e] with s hs
      rw [hs, zpow_natCast, smul_eq_mul]
    have hL := eventually_logDeriv_eq_of_eq_zpow_mul hξ₁a hξ₁0 hξloc
    have hHx : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) p := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      exact Eventually.of_forall hcpowd
    have hΨ : DifferentiableAt ℂ (fun s => deriv ξ₁ s / ξ₁ s * (x : ℂ) ^ s) p :=
      (hξ₁a.deriv.differentiableAt.div hξ₁a.differentiableAt hξ₁0).mul (hcpowd p)
    obtain ⟨φ, hφ, hφe⟩ := exists_eventually_eq_div_sub_add_of_analyticAt (c := (mo p : ℂ)) hHx hΨ
      (F := F) (by
      filter_upwards [hL] with s hs
      simp only [logDeriv_apply] at hs
      simp only [F]
      rw [hs]
      push_cast
      ring)
    exact ⟨φ, hφ, hφe⟩
  let z0 : ℂ := ⟨a, c⟩
  let w0 : ℂ := ⟨b, d⟩
  have hKre : ∀ s ∈ Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im,
      a ≤ s.re ∧ s.re ≤ b ∧ c ≤ s.im ∧ s.im ≤ d := by
    intro s hs
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hs
    rw [show z0.re = a from rfl, show w0.re = b from rfl, Set.uIcc_of_le hab] at h1
    rw [show z0.im = c from rfl, show w0.im = d from rfl, Set.uIcc_of_le hcd] at h2
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hdiff : ∀ s ∈ Set.uIcc z0.re w0.re ×ℂ Set.uIcc z0.im w0.im, s ∉ Z →
      DifferentiableAt ℂ F s := by
    intro s hsK hsZ
    obtain ⟨k1, k2, k3, k4⟩ := hKre s hsK
    have hHs : H s ≠ 0 := fun h0 => hsZ (hZ2 s k1 k2 k3 k4 h0)
    exact (((hH.analyticAt s).deriv.differentiableAt).div (hH s) hHs).mul (hcpowd s)
  obtain ⟨g, hg, hfg⟩ := exists_differentiableOn_eq_add_sum_div_sub _ Z r F hloc
    fun s hs hsS => (hdiff s hs hsS).differentiableWithinAt
  have hin : ∀ p ∈ Z, z0.re < p.re ∧ p.re < w0.re ∧ z0.im < p.im ∧ p.im < w0.im := by
    intro p hp
    exact hZ p hp
  have hRS := integral_boundary_rect_add_sum_div_sub Z r F g hin hg hfg
  exact hRS

open Complex in
private lemma intervalIntegral_conj_eq (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, starRingEnd ℂ (f x) = starRingEnd ℂ (∫ x in a..b, f x) := by
  simp only [intervalIntegral, integral_conj, map_sub]

open Complex in
/-- **The two vertical sides.** With `s = 3/2 + iy` on the right and `-1/2 + iy` on the left,
`I ∫_right H'/H n^s - I ∫_left H'/H n^s = -I (B - A) Λ(n) + O(n^{3/2} log)`, uniformly. -/
private lemma vertical_sides_eq (F G H : ℂ → ℂ) (m : ℕ) (hFd : DifferentiableOn ℂ F {1}ᶜ)
    (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s) (D : FunctionalEquation F)
    (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Complex.Gamma (D.α i * s + D.r i)) * G s)
    (hrefl : ∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s))
    (hFne : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (Λ : ℕ → ℂ) (hΛ : ∀ s : ℂ, 1 < s.re → LSeriesHasSum Λ s (-deriv F s / F s))
    (θ₁ C₁ : ℝ) (hθ : θ₁ < 1 / 2) (hC₁ : 0 ≤ C₁) (hΛb : ∀ k : ℕ, k ≠ 0 → ‖Λ k‖ ≤ C₁ * (k : ℝ) ^ θ₁)
        :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n → ∀ A B : ℝ, A ≤ 0 → 0 ≤ B →
      ‖(I • (∫ y : ℝ in A..B, deriv H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in A..B, deriv H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) -
        I * (-(((B - A : ℝ) : ℂ) * Λ n))‖ ≤
        K * (n : ℝ) ^ (3 / 2 : ℝ) * (1 + Real.log (1 + |A|) + Real.log (1 + B)) := by
  obtain ⟨KR, hKR0, hKR⟩ := norm_integral_exp_mul_archimedean_le m D.Q D.α D.r D.α_pos D.r_re_nonneg
  obtain ⟨hsumΛ, KΛ, hKΛ0, hKΛ⟩ := integral_LSeries_line_three_halves_mul_exp Λ θ₁ C₁ hθ hC₁ hΛb
  have hw0 : D.w ≠ 0 := by
    intro h; have := D.norm_w; rw [h, norm_zero] at this; norm_num at this
  refine ⟨2 * (KR + KΛ), by positivity, fun n hn A B hA hB => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogn0 : 0 < Real.log n := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlogn
  set s : ℝ → ℂ := fun t => ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : ∀ t, (s t).re = 3 / 2 := fun t => by simp [s]
  have hsc : Continuous s := by simp only [s]; fun_prop
  set R : ℝ → ℂ := fun t => (m : ℂ) / s t + Complex.log D.Q +
    (∑ i, (D.α i : ℂ) * digamma (D.α i * s t + D.r i)) + (m : ℂ) / (s t - 1) with hR
  set Lf : ℝ → ℂ := fun t => LSeries Λ (s t) with hLf
  set ℓ : ℝ → ℂ := fun t => deriv H (s t) / H (s t) with hℓ
  have hℓeq : ∀ t, ℓ t = R t - Lf t := by
    intro t
    have h1 : 1 < (s t).re := by rw [hsre]; norm_num
    have hs1 : s t ≠ 1 := fun h => by
      have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
    have hL := logDeriv_completed F G H m hFd hGF D hHr (s t) (by linarith) hs1 (hFne _ h1)
    have hΛs := (hΛ (s t) h1).LSeries_eq
    simp only [ℓ, R, Lf]
    rw [← logDeriv_apply, hL, logDeriv_apply, hΛs]
    ring
  have hleft : ∀ t : ℝ, deriv H (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) /
      H (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = -starRingEnd ℂ (ℓ t) := by
    intro t
    have e : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I = 1 - starRingEnd ℂ (s t) := by
      simp only [s, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [e, ← logDeriv_apply, logDeriv_one_sub_conj_eq_neg_conj H D.w hHd hw0 hrefl (s t),
        logDeriv_apply]
  -- continuity
  have hRc : Continuous R := by
    have hs0 : ∀ t, s t ≠ 0 := fun t h => by have := hsre t; rw [h] at this; norm_num at this
    have hs10 : ∀ t, s t - 1 ≠ 0 := fun t h => by
      have := congrArg Complex.re h; simp [s] at this; norm_num at this
    have hargre : ∀ i t, 0 < ((D.α i : ℂ) * s t + D.r i).re := fun i t => by
      simp only [Complex.add_re, Complex.re_ofReal_mul, hsre]
      have := D.α_pos i; have := D.r_re_nonneg i; positivity
    have hψc : ∀ i, Continuous fun t => Complex.digamma ((D.α i : ℂ) * s t + D.r i) := fun i =>
      continuous_iff_continuousAt.mpr fun t =>
        (continuousAt_digamma_of_re_pos (hargre i t)).comp (f := fun t => (D.α i : ℂ) * s t + D.r i)
          (by fun_prop)
    simp only [R]
    refine (((continuous_const.div hsc hs0).add continuous_const).add
      (continuous_finsetSum _ fun i _ => continuous_const.mul (hψc i))).add
      (continuous_const.div (hsc.sub continuous_const) hs10)
  have hLfc : Continuous Lf := hsumΛ.continuous_vertical
  -- the exponentials
  set ep : ℝ → ℂ := fun t => Complex.exp ((Real.log n : ℂ) * I * t) with hep
  set em : ℝ → ℂ := fun t => Complex.exp (((-Real.log n : ℝ) : ℂ) * I * t) with hem
  have hepc : Continuous ep := by simp only [ep]; fun_prop
  have hemc : Continuous em := by simp only [em]; fun_prop
  have hemconj : ∀ t, starRingEnd ℂ (em t) = ep t := by
    intro t
    simp only [em, ep, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1; push_cast; ring
  have hcpR : ∀ t, ((n : ℝ) : ℂ) ^ (s t) = (((n : ℝ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) * ep t := by
    intro t
    rw [ofReal_cpow_eq_exp hn0, Real.rpow_def_of_pos hn0, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; simp only [s]; push_cast; ring
  have hcpL : ∀ t : ℝ, ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * ep t := by
    intro t
    rw [ofReal_cpow_eq_exp hn0, Real.rpow_def_of_pos hn0, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  set N3 : ℝ := (n : ℝ) ^ (3 / 2 : ℝ) with hN3
  set N1 : ℝ := (n : ℝ) ^ (-(1 / 2) : ℝ) with hN1
  have hN3pos : 0 < N3 := by positivity
  have hN1pos : 0 < N1 := by positivity
  have hN1le : N1 ≤ N3 := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
    (by norm_num)
  have hN3inv : N3 * (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by
    rw [hN3, ← Real.rpow_add hn0]; norm_num
  -- the right integral
  have hRight : (∫ y : ℝ in A..B, deriv H (s y) / H (s y) * ((n : ℝ) : ℂ) ^ (s y)) =
      (N3 : ℂ) * ((∫ t in A..B, ep t * R t) - ∫ t in A..B, Lf t * ep t) := by
    have e1 : (fun y : ℝ => deriv H (s y) / H (s y) * ((n : ℝ) : ℂ) ^ (s y)) =
        fun t => (N3 : ℂ) * (ep t * R t - Lf t * ep t) := by
      funext t
      rw [hcpR]
      change ℓ t * _ = _
      rw [hℓeq]; ring
    rw [e1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun t => ep t * R t) (g := fun t => Lf t * ep t)
        ((hepc.mul hRc).intervalIntegrable _ _) ((hLfc.mul hepc).intervalIntegrable _ _)]
  -- the left integral
  have hLeft : (∫ y : ℝ in A..B, deriv H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
        ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
      -((N1 : ℂ) * starRingEnd ℂ ((∫ t in A..B, em t * R t) - ∫ t in A..B, Lf t * em t)) := by
    have e1 : (fun y : ℝ => deriv H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
        H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
        ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
        fun t => -((N1 : ℂ) * starRingEnd ℂ (em t * R t - Lf t * em t)) := by
      funext t
      rw [hleft, hcpL, hℓeq]
      simp only [map_sub, map_mul, hemconj]
      ring
    rw [e1, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral_conj_eq,
      intervalIntegral.integral_sub (f := fun t => em t * R t) (g := fun t => Lf t * em t)
        ((hemc.mul hRc).intervalIntegrable _ _) ((hLfc.mul hemc).intervalIntegrable _ _)]
  change ‖(I • (∫ y : ℝ in A..B, deriv H (s y) / H (s y) * ((n : ℝ) : ℂ) ^ (s y)) - _) - _‖ ≤ _
  rw [hRight, hLeft]
  -- the estimates
  set X : ℝ := 1 + Real.log (1 + |A|) + Real.log (1 + B) with hX
  have hl1 : 0 ≤ Real.log (1 + |A|) := Real.log_nonneg (by linarith [abs_nonneg A])
  have hl2 : 0 ≤ Real.log (1 + B) := Real.log_nonneg (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hRp : ‖∫ t in A..B, ep t * R t‖ ≤ KR * X := by
    have := hKR (Real.log n) (by rw [abs_of_pos hlogn0]; exact hlogn) A B hA hB
    exact this
  have hRm : ‖∫ t in A..B, em t * R t‖ ≤ KR * X := by
    have := hKR (-Real.log n) (by rw [abs_neg, abs_of_pos hlogn0]; exact hlogn) A B hA hB
    exact this
  obtain ⟨hΛp, hΛm⟩ := hKΛ n hn A B
  have hΛp' : ‖(∫ t in A..B, Lf t * ep t) -
      ((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)‖ ≤ KΛ := hΛp
  have hΛm' : ‖∫ t in A..B, Lf t * em t‖ ≤ KΛ := hΛm
  have key : (I • ((N3 : ℂ) * ((∫ t in A..B, ep t * R t) - ∫ t in A..B, Lf t * ep t)) -
      I • -((N1 : ℂ) * starRingEnd ℂ ((∫ t in A..B, em t * R t) - ∫ t in A..B, Lf t * em t))) -
      I * (-(((B - A : ℝ) : ℂ) * Λ n)) =
      I * ((N3 : ℂ) * (∫ t in A..B, ep t * R t) -
        (N3 : ℂ) * ((∫ t in A..B, Lf t * ep t) -
          ((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) +
        (N1 : ℂ) * starRingEnd ℂ ((∫ t in A..B, em t * R t) - ∫ t in A..B, Lf t * em t)) := by
    have h1 : (N3 : ℂ) * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hN3inv
    simp only [smul_eq_mul]
    linear_combination (-(I * ((B - A : ℝ) : ℂ) * Λ n)) * h1
  rw [key, norm_mul, Complex.norm_I, one_mul]
  have hN3n : ‖(N3 : ℂ)‖ = N3 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN3pos]
  have hN1n : ‖(N1 : ℂ)‖ = N1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN1pos]
  calc _ ≤ ‖(N3 : ℂ) * (∫ t in A..B, ep t * R t)‖ +
        ‖(N3 : ℂ) * ((∫ t in A..B, Lf t * ep t) -
          ((B - A : ℝ) : ℂ) * Λ n * (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ))‖ +
        ‖(N1 : ℂ) * starRingEnd ℂ ((∫ t in A..B, em t * R t) - ∫ t in A..B, Lf t * em t)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ N3 * (KR * X) + N3 * KΛ + N1 * (KR * X + KΛ) := by
        rw [norm_mul, norm_mul, norm_mul, hN3n, hN1n, Complex.norm_conj]
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add hRm hΛm')
    _ ≤ 2 * (KR + KΛ) * N3 * X := by
        have h1 : N1 * (KR * X + KΛ) ≤ N3 * (KR * X + KΛ) := by
          gcongr
        have h2 : N3 * KΛ ≤ N3 * KΛ * X := by
          have : 0 ≤ N3 * KΛ := by positivity
          nlinarith
        nlinarith [mul_nonneg hN3pos.le (mul_nonneg hKR0 (by linarith : (0:ℝ) ≤ X))]

/-- `Λ = log · b` off `0`, from uniqueness of Dirichlet coefficients. -/
private lemma eq_logMul_of_neg_logDeriv (a : ArithmeticFunction ℂ) (F : ℂ → ℂ) (hF :
    IsLSeriesContinuation a F)
    (b : ℕ → ℂ) (hlog : IsEulerLog a b) (Λ : ℕ → ℂ)
    (hΛ : ∀ s : ℂ, 1 < s.re → LSeriesHasSum Λ s (-deriv F s / F s)) :
    ∀ k : ℕ, k ≠ 0 → Λ k = (Real.log k : ℂ) * b k := by
  intro k hk
  have hB : LSeries.abscissaOfAbsConv b ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hlog.2 y (by simpa using hy)).1
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have key : ∀ s : ℂ, 1 < s.re → LSeries Λ s = LSeries (LSeries.logMul b) s := by
    intro s hs
    rw [(hΛ s hs).LSeries_eq]
    have hlt : LSeries.abscissaOfAbsConv b < s.re := lt_of_le_of_lt hB (by exact_mod_cast hs)
    have h1 := (LSeries_hasDerivAt hlt).cexp
    have heq : (fun z => Complex.exp (LSeries b z)) =ᶠ[nhds s] F := by
      filter_upwards [hU.mem_nhds hs] with z hz
      rw [hF.1 z hz, (hlog.2 z hz).2]
    have h2 := h1.congr_of_eventuallyEq heq.symm
    rw [h2.deriv, hF.1 s hs, (hlog.2 s hs).2]
    have := Complex.exp_ne_zero (LSeries b s)
    field_simp
  have hΛa : LSeries.abscissaOfAbsConv Λ < ⊤ :=
    lt_of_le_of_lt ((hΛ 2 (by norm_num)).LSeriesSummable.abscissaOfAbsConv_le) (EReal.coe_lt_top _)
  have hLa : LSeries.abscissaOfAbsConv (LSeries.logMul b) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact lt_of_le_of_lt hB (EReal.coe_lt_top 1)
  have := LSeries.eq_of_LSeries_eventually_eq hΛa hLa (by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    exact key x (by simpa using hx)) hk
  rw [this, LSeries.logMul, ← Complex.natCast_log]

/-- The coefficient bound `‖Λ k‖ ≤ C₁ k^θ₁` with `θ₁ < 1/2`. -/
private lemma norm_logMul_le_rpow (b : ℕ → ℂ) (θ Cb : ℝ) (hθ : θ < 1 / 2)
    (hbC : ∀ n, ‖b n‖ ≤ Cb * (n : ℝ) ^ θ) (Λ : ℕ → ℂ)
    (hΛ : ∀ k : ℕ, k ≠ 0 → Λ k = (Real.log k : ℂ) * b k) :
    ∃ θ₁ C₁ : ℝ, θ₁ < 1 / 2 ∧ 0 ≤ C₁ ∧ ∀ k : ℕ, k ≠ 0 → ‖Λ k‖ ≤ C₁ * (k : ℝ) ^ θ₁ := by
  set δ : ℝ := (1 / 2 - θ) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  refine ⟨θ + δ, |Cb| / δ, by rw [hδ]; linarith, by positivity, fun k hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  rw [hΛ k hk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hk1)]
  have h1 : Real.log k ≤ (k : ℝ) ^ δ / δ := Real.log_le_rpow_div hk0.le hδ0
  have h2 : ‖b k‖ ≤ |Cb| * (k : ℝ) ^ θ :=
    (hbC k).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc Real.log k * ‖b k‖ ≤ ((k : ℝ) ^ δ / δ) * (|Cb| * (k : ℝ) ^ θ) := by
        gcongr
    _ = |Cb| / δ * ((k : ℝ) ^ θ * (k : ℝ) ^ δ) := by ring
    _ = |Cb| / δ * (k : ℝ) ^ (θ + δ) := by rw [Real.rpow_add hk0]

open Complex in
/-- The archimedean part of `H'/H` is `O(log |t|)` in `1/2 ≤ σ ≤ 3/2`. -/
private lemma norm_archimedean_le_log (m : ℕ) (Q : ℝ) {d : ℕ} (α : Fin d → ℝ) (r : Fin d → ℂ)
    (hα : ∀ i, 0 < α i) (hr : ∀ i, 0 ≤ (r i).re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖(m : ℂ) / s + Complex.log Q + (∑ i, (α i : ℂ) * digamma (α i * s + r i)) +
        (m : ℂ) / (s - 1)‖ ≤ K * Real.log |s.im| := by
  obtain ⟨Cd, hCd⟩ := Complex.exists_norm_digamma_sub_log_le (Real.pi / 2) (by positivity)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : Fin d → ℝ := fun i => |Real.log (α i / 2)| + |Real.log (2 * α i + ‖r i‖)| + Real.pi +
    2 * |Cd| / α i with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i => by have := hα i; simp only [c]; positivity
  refine ⟨(2 * m + ‖Complex.log Q‖ + ∑ i, α i * c i) / Real.log 2 + ∑ i, α i, by
    have : 0 ≤ ∑ i, α i * c i := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (hc0 i)
    have : 0 ≤ ∑ i, α i := Finset.sum_nonneg fun i _ => (hα i).le
    positivity, fun s h1 h2 ht => ?_⟩
  have hL : Real.log 2 ≤ Real.log |s.im| := Real.log_le_log (by norm_num) ht
  have hL0 : 0 < Real.log |s.im| := lt_of_lt_of_le hl2 hL
  have hsn : 2 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
  have hs1n : 2 ≤ ‖s - 1‖ := ht.trans (by simpa using Complex.abs_im_le_norm (s - 1))
  have hb1 : ‖(m : ℂ) / s‖ ≤ m := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
    nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hb2 : ‖(m : ℂ) / (s - 1)‖ ≤ m := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
    nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hψ : ∀ i, ‖(α i : ℂ) * digamma (α i * s + r i)‖ ≤ α i * (c i + Real.log |s.im|) := by
    intro i
    set w : ℂ := (α i : ℂ) * s + r i with hw
    have hwre : α i / 2 ≤ w.re := by
      simp only [w, Complex.add_re, Complex.re_ofReal_mul]
      have := hα i; have := hr i; nlinarith
    have hαi := hα i
    have hw1 : α i / 2 ≤ ‖w‖ := hwre.trans (Complex.re_le_norm w)
    have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw1; linarith
    have hw2 : ‖w‖ ≤ (2 * α i + ‖r i‖) * |s.im| := by
      have h3 : ‖s‖ ≤ 3 / 2 + |s.im| := by
        have := Complex.norm_le_abs_re_add_abs_im s
        rw [abs_of_pos (by linarith)] at this; linarith
      calc ‖w‖ ≤ ‖(α i : ℂ) * s‖ + ‖r i‖ := norm_add_le _ _
        _ = α i * ‖s‖ + ‖r i‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
            hαi]
        _ ≤ α i * (3 / 2 + |s.im|) + ‖r i‖ := by gcongr
        _ ≤ (2 * α i + ‖r i‖) * |s.im| := by nlinarith [norm_nonneg (r i)]
    have harg : |Complex.arg w| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
    have hE := hCd w hw0 (by linarith [(abs_lt.mp harg).1]) (by linarith [(abs_lt.mp harg).2])
    have hE' : ‖Complex.digamma w - Complex.log w‖ ≤ 2 * |Cd| / α i := by
      refine hE.trans ?_
      calc Cd / ‖w‖ ≤ |Cd| / ‖w‖ := by gcongr; exact le_abs_self _
        _ ≤ |Cd| / (α i / 2) := by gcongr
        _ = 2 * |Cd| / α i := by field_simp
    have hlogw : ‖Complex.log w‖ ≤ |Real.log (α i / 2)| + |Real.log (2 * α i + ‖r i‖)| +
        Real.log |s.im| + Real.pi := by
      have hwpos : 0 < ‖w‖ := by linarith
      have hup : Real.log ‖w‖ ≤ Real.log (2 * α i + ‖r i‖) + Real.log |s.im| := by
        rw [← Real.log_mul (by positivity) (by linarith)]
        exact Real.log_le_log hwpos hw2
      have hlo : Real.log (α i / 2) ≤ Real.log ‖w‖ := Real.log_le_log (by positivity) hw1
      have habs : |Real.log ‖w‖| ≤ |Real.log (α i / 2)| + |Real.log (2 * α i + ‖r i‖)| +
          Real.log |s.im| := by
        rw [abs_le]; constructor
        · linarith [neg_abs_le (Real.log (α i / 2)), abs_nonneg (Real.log (2 * α i + ‖r i‖))]
        · linarith [le_abs_self (Real.log (2 * α i + ‖r i‖)), abs_nonneg (Real.log (α i / 2))]
      calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ _ := by
          rw [Complex.log_re, Complex.log_im]
          linarith [Complex.abs_arg_le_pi w]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hαi]
    apply mul_le_mul_of_nonneg_left _ hαi.le
    calc ‖Complex.digamma w‖ ≤ ‖Complex.digamma w - Complex.log w‖ + ‖Complex.log w‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ 2 * |Cd| / α i + (|Real.log (α i / 2)| + |Real.log (2 * α i + ‖r i‖)| +
          Real.log |s.im| + Real.pi) := add_le_add hE' hlogw
      _ = c i + Real.log |s.im| := by simp only [c]; ring
  have hsum : ‖∑ i, (α i : ℂ) * digamma (α i * s + r i)‖ ≤
      (∑ i, α i * c i) + (∑ i, α i) * Real.log |s.im| := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hψ i).trans (le_of_eq ?_)
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hconst : 2 * (m : ℝ) + ‖Complex.log Q‖ + ∑ i, α i * c i ≤
      (2 * m + ‖Complex.log Q‖ + ∑ i, α i * c i) / Real.log 2 * Real.log |s.im| := by
    have h0 : 0 ≤ 2 * (m : ℝ) + ‖Complex.log Q‖ + ∑ i, α i * c i := by
      have : 0 ≤ ∑ i, α i * c i := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (hc0 i)
      positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    nlinarith
  calc _ ≤ ‖(m : ℂ) / s‖ + ‖Complex.log Q‖ + ‖∑ i, (α i : ℂ) * digamma (α i * s + r i)‖ +
        ‖(m : ℂ) / (s - 1)‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_add_le _ _
    _ ≤ m + ‖Complex.log Q‖ + ((∑ i, α i * c i) + (∑ i, α i) * Real.log |s.im|) + m := by
        gcongr
    _ ≤ _ := by
        have hm : (m : ℝ) ≤ m / Real.log 2 * Real.log |s.im| := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
        have e : ((2 * m + ‖Complex.log Q‖ + ∑ i, α i * c i) / Real.log 2 + ∑ i, α i) *
            Real.log |s.im| = (2 * m + ‖Complex.log Q‖ + ∑ i, α i * c i) / Real.log 2 *
              Real.log |s.im| + (∑ i, α i) * Real.log |s.im| := by ring
        rw [e]
        have hm2 : (m : ℝ) / Real.log 2 * Real.log |s.im| ≤
            (2 * m + ‖Complex.log Q‖ + ∑ i, α i * c i) / Real.log 2 * Real.log |s.im| := by
          have : 0 ≤ ∑ i, α i * c i := Finset.sum_nonneg fun i _ => mul_nonneg (hα i).le (hc0 i)
          gcongr
          linarith [norm_nonneg (Complex.log Q)]
        nlinarith

open Complex in
/-- A horizontal segment `[-1/2, 3/2] + iy` of the contour. -/
private lemma norm_horizontal_segment_le (f : ℂ → ℂ) (x y M : ℝ) (hx : 1 ≤ x)
    (hM : ∀ u : ℝ, -1 / 2 ≤ u → u ≤ 3 / 2 → ‖f ((u : ℂ) + (y : ℂ) * I)‖ ≤ M) :
    ‖∫ u : ℝ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), f ((u : ℂ) + (y : ℂ) * I) *
        (x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I)‖ ≤ 2 * (x ^ (3 / 2 : ℝ) * M) := by
  have hx0 : 0 < x := by linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 / 2 : ℝ)) (b := 3 / 2)
    (C := x ^ (3 / 2 : ℝ) * M) (f := fun u : ℝ => f ((u : ℂ) + (y : ℂ) * I) *
      (x : ℂ) ^ ((u : ℂ) + (y : ℂ) * I)) (fun u hu => by
      rw [Set.uIoc_of_le (by norm_num)] at hu
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      have h1 := hM u (by linarith [hu.1]) hu.2
      have hM0 : 0 ≤ M := (norm_nonneg _).trans h1
      have h2 : x ^ u ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hu.2
      rw [mul_comm]
      exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity))
  rw [show |(3 / 2 : ℝ) - (-1 / 2)| = 2 by norm_num] at this
  linarith

/-- Two weighted zero sums with the same zeros and multiplicities off a finite set `X`. -/
private lemma finsum_zeros_eq_of_eqOn_compl (f h : ℂ → ℂ) (wt : ℂ → ℂ) (X : Finset ℂ) (S : Set ℂ)
    (W : ℝ)
    (hSf : {ρ | f ρ = 0 ∧ ρ ∈ S}.Finite) (hSh : {ρ | h ρ = 0 ∧ ρ ∈ S}.Finite)
    (heq : ∀ ρ ∈ S, ρ ∉ X →
      ((f ρ = 0 ↔ h ρ = 0) ∧ analyticOrderNatAt f ρ = analyticOrderNatAt h ρ))
    (hW : ∀ x ∈ X, ‖wt x‖ ≤ W) :
    ‖(∑ᶠ ρ ∈ {ρ | f ρ = 0 ∧ ρ ∈ S}, (analyticOrderNatAt f ρ : ℂ) * wt ρ) -
        (∑ᶠ ρ ∈ {ρ | h ρ = 0 ∧ ρ ∈ S}, (analyticOrderNatAt h ρ : ℂ) * wt ρ)‖ ≤
      (∑ x ∈ X, ((analyticOrderNatAt f x : ℝ) + analyticOrderNatAt h x)) * W := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hSh]
  set Af := hSf.toFinset
  set Ah := hSh.toFinset
  rw [← Finset.sum_filter_add_sum_filter_not Af (· ∈ X),
    ← Finset.sum_filter_add_sum_filter_not Ah (· ∈ X)]
  have hfil : Af.filter (· ∉ X) = Ah.filter (· ∉ X) := by
    ext ρ
    simp only [Finset.mem_filter, Af, Ah, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, hS⟩, hX⟩; exact ⟨⟨(heq ρ hS hX).1.1 h0, hS⟩, hX⟩
    · rintro ⟨⟨h0, hS⟩, hX⟩; exact ⟨⟨(heq ρ hS hX).1.2 h0, hS⟩, hX⟩
  have hsum : ∑ ρ ∈ Af.filter (· ∉ X), (analyticOrderNatAt f ρ : ℂ) * wt ρ =
      ∑ ρ ∈ Ah.filter (· ∉ X), (analyticOrderNatAt h ρ : ℂ) * wt ρ := by
    rw [hfil]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    simp only [Finset.mem_filter, Ah, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ
    rw [(heq ρ hρ.1.2 hρ.2).2]
  rw [hsum, add_sub_add_right_eq_sub]
  have hW0 : ∀ x ∈ X, 0 ≤ W := fun x hx => (norm_nonneg _).trans (hW x hx)
  have b1 : ‖∑ ρ ∈ Af.filter (· ∈ X), (analyticOrderNatAt f ρ : ℂ) * wt ρ‖ ≤
      (∑ x ∈ X, (analyticOrderNatAt f x : ℝ)) * W := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (Finset.mem_filter.1 hρ).2)
        fun x hx _ => mul_nonneg (Nat.cast_nonneg _) (hW0 x hx))
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hW ρ (Finset.mem_filter.1 hρ).2) (Nat.cast_nonneg _)
  have b2 : ‖∑ ρ ∈ Ah.filter (· ∈ X), (analyticOrderNatAt h ρ : ℂ) * wt ρ‖ ≤
      (∑ x ∈ X, (analyticOrderNatAt h x : ℝ)) * W := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (Finset.mem_filter.1 hρ).2)
        fun x hx _ => mul_nonneg (Nat.cast_nonneg _) (hW0 x hx))
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hW ρ (Finset.mem_filter.1 hρ).2) (Nat.cast_nonneg _)
  calc _ ≤ ‖∑ ρ ∈ Af.filter (· ∈ X), (analyticOrderNatAt f ρ : ℂ) * wt ρ‖ +
        ‖∑ ρ ∈ Ah.filter (· ∈ X), (analyticOrderNatAt h ρ : ℂ) * wt ρ‖ := norm_sub_le _ _
    _ ≤ _ := by
        rw [Finset.sum_add_distrib, add_mul]
        exact add_le_add b1 b2

open Complex in
/-- On a horizontal segment `[-1/2, 3/2] ± iT'` at a good height, `H ≠ 0` and
`H'/H = O(log² T)`. -/
private lemma norm_logDeriv_horizontal_le (F G H : ℂ → ℂ) (m : ℕ) (D : FunctionalEquation F)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Complex.Gamma (D.α i * s + D.r i)) * G s)
    (hHrefl : ∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s))
    (KR : ℝ) (hKR0 : 0 ≤ KR)
    (hRb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖(m : ℂ) / s + Complex.log D.Q + (∑ i, (D.α i : ℂ) * digamma (D.α i * s + D.r i)) +
        (m : ℂ) / (s - 1)‖ ≤ KR * Real.log |s.im|)
    (KG T : ℝ) (hT8 : 8 ≤ T) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (T' : ℝ) (hT'1 : T < T')
    (hT'2 : T' < T + 1)
    (hg : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 → G (u + ε * T' * I) ≠ 0 ∧
      ‖deriv G (u + ε * T' * I) / G (u + ε * T' * I)‖ ≤ KG * Real.log T ^ 2) :
    ∀ u : ℝ, -1 / 2 ≤ u → u ≤ 3 / 2 →
      H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖deriv H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) / H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I)‖ ≤
        2 * KR * Real.log T + KG * Real.log T ^ 2 + m := by
  have hw0 : D.w ≠ 0 := by
    intro h; have := D.norm_w; rw [h, norm_zero] at this; norm_num at this
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hT'pos : 0 < T' := by linarith
  have hright : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 →
      H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖deriv H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) /
        H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I)‖ ≤
        2 * KR * Real.log T + KG * Real.log T ^ 2 + m := by
    intro u hu1 hu2
    set z : ℂ := (u : ℂ) + ((ε * T' : ℝ) : ℂ) * I with hz
    have hz' : z = u + ε * T' * I := by simp only [z]; push_cast; ring
    obtain ⟨hGz, hGb⟩ := hg u hu1 hu2
    rw [← hz'] at hGz hGb
    have hzre : z.re = u := by simp [z]
    have hzim : z.im = ε * T' := by simp [z]
    have hzima : |z.im| = T' := by rw [hzim, abs_mul, hεa, one_mul, abs_of_pos hT'pos]
    have hz1 : z ≠ 1 := fun h => by
      have h' : ε * T' = 0 := by rw [← hzim, h, Complex.one_im]
      rcases hε with rfl | rfl <;> linarith
    have hz0 : z ≠ 0 := fun h => by rw [h] at hzre; simp at hzre; linarith
    have hFz : F z ≠ 0 := fun h => hGz (by rw [hGF z hz1, h, mul_zero])
    have hQ0 : (D.Q : ℂ) ≠ 0 := by exact_mod_cast D.Q_pos.ne'
    have hHz : H z ≠ 0 := by
      rw [hHr z (by rw [hzre]; linarith)]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hz0)
        ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero hz0).mpr hQ0))
        (Finset.prod_ne_zero_iff.2 fun i _ => Complex.Gamma_ne_zero_of_re_pos ?_)) hGz
      simp only [Complex.add_re, Complex.re_ofReal_mul, hzre]
      have := D.α_pos i; have := D.r_re_nonneg i; nlinarith
    refine ⟨hHz, ?_⟩
    have hL := logDeriv_completed F G H m hFd hGF D hHr z (by rw [hzre]; linarith) hz1 hFz
    have hGFl : logDeriv G z = (m : ℂ) / (z - 1) + logDeriv F z := by
      have hev : G =ᶠ[nhds z] fun w => (w - 1) ^ m * F w := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
        exact hGF w hw
      rw [(logDeriv_congr_nhds hev).eq_of_nhds]
      have hFda : DifferentiableAt ℂ F z :=
        hFd.differentiableAt (isOpen_compl_singleton.mem_nhds hz1)
      rw [logDeriv_fun_mul (f := fun w : ℂ => (w - 1) ^ m) (g := F) z
        (pow_ne_zero _ (sub_ne_zero.2 hz1)) hFz ((differentiableAt_id.sub_const 1).pow m) hFda,
        logDeriv_fun_pow (f := fun w : ℂ => w - 1) (differentiableAt_id.sub_const 1) m,
        logDeriv_apply (fun w : ℂ => w - 1)]
      have : deriv (fun w : ℂ => w - 1) z = 1 := by
        simp
      rw [this]; ring
    rw [← logDeriv_apply, hL]
    have hR := hRb z (by rw [hzre]; exact hu1) (by rw [hzre]; exact hu2)
      (by rw [hzima]; linarith)
    rw [hzima] at hR
    have hlogT' : Real.log T' ≤ 2 * Real.log T := by
      rw [← Real.log_rpow (by linarith)]
      apply Real.log_le_log hT'pos
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
    have hmz : ‖(m : ℂ) / (z - 1)‖ ≤ m := by
      have h1 : 1 ≤ ‖z - 1‖ := by
        have := Complex.abs_im_le_norm (z - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero, hzima] at this; linarith
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
      nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hFl : logDeriv F z = logDeriv G z - (m : ℂ) / (z - 1) := by rw [hGFl]; ring
    rw [hFl]
    have hGb' : ‖logDeriv G z‖ ≤ KG * Real.log T ^ 2 := by rw [logDeriv_apply]; exact hGb
    calc ‖(m : ℂ) / z + Complex.log D.Q +
          (∑ i, (D.α i : ℂ) * digamma (D.α i * z + D.r i)) + (m : ℂ) / (z - 1) +
          (logDeriv G z - (m : ℂ) / (z - 1))‖
        ≤ ‖(m : ℂ) / z + Complex.log D.Q +
          (∑ i, (D.α i : ℂ) * digamma (D.α i * z + D.r i)) + (m : ℂ) / (z - 1)‖ +
          (‖logDeriv G z‖ + ‖(m : ℂ) / (z - 1)‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
      _ ≤ KR * Real.log T' + (KG * Real.log T ^ 2 + m) := add_le_add hR (add_le_add hGb' hmz)
      _ ≤ 2 * KR * Real.log T + KG * Real.log T ^ 2 + m := by
          have := mul_le_mul_of_nonneg_left hlogT' hKR0
          linarith
  intro u hu1 hu2
  rcases le_or_gt (1 / 2) u with hu | hu
  · exact hright u hu hu2
  · obtain ⟨h1, h2⟩ := hright (1 - u) (by linarith) (by linarith)
    have e : (u : ℂ) + ((ε * T' : ℝ) : ℂ) * I =
        1 - starRingEnd ℂ (((1 - u : ℝ) : ℂ) + ((ε * T' : ℝ) : ℂ) * I) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have hne : H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) ≠ 0 := by
      rw [e, hHrefl]; exact mul_ne_zero hw0 ((map_ne_zero _).2 h1)
    refine ⟨hne, ?_⟩
    have hld : deriv H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) / H ((u : ℂ) + ((ε * T' : ℝ) : ℂ) * I) =
        -starRingEnd ℂ (deriv H (((1 - u : ℝ) : ℂ) + ((ε * T' : ℝ) : ℂ) * I) /
          H (((1 - u : ℝ) : ℂ) + ((ε * T' : ℝ) : ℂ) * I)) := by
      rw [← logDeriv_apply, ← logDeriv_apply, e, logDeriv_one_sub_conj_eq_neg_conj H D.w hHd hw0
          hHrefl]
    rw [hld, norm_neg, Complex.norm_conj]
    exact h2

open Complex in
/-- The contour identity solved for the zero sum. -/
private lemma zero_sum_eq_of_contour {Bot Top Rt Lt S Λn : ℂ} {T₁ T₂ b V : ℝ}
    (hres : Bot - Top + I • Rt - I • Lt = 2 * (Real.pi : ℂ) * I * S)
    (hV : ‖(I • Rt - I • Lt) - I * (-(((T₁ - -T₂ : ℝ) : ℂ) * Λn))‖ ≤ V)
    (hB : ‖Bot‖ ≤ b) (hT : ‖Top‖ ≤ b) :
    ‖S + (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λn‖ ≤ (2 * b + V) / (2 * Real.pi) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkey : S + (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λn =
      (Bot - Top + ((I • Rt - I • Lt) - I * (-(((T₁ - -T₂ : ℝ) : ℂ) * Λn)))) /
        (2 * (Real.pi : ℂ) * I) := by
    rw [eq_div_iff (by simp [hpi, Complex.I_ne_zero])]
    push_cast
    field_simp
    simp only [smul_eq_mul] at hres ⊢
    linear_combination -hres
  rw [hkey, norm_div]
  have h2pi : ‖2 * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]; simp
  rw [h2pi]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ‖Bot - Top + ((I • Rt - I • Lt) - I * (-(((T₁ - -T₂ : ℝ) : ℂ) * Λn)))‖
      ≤ ‖Bot‖ + ‖Top‖ + ‖(I • Rt - I • Lt) - I * (-(((T₁ - -T₂ : ℝ) : ℂ) * Λn))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 2 * b + V := by linarith

/-- The real inequality closing the rectangle estimate. -/
private lemma rectangle_real_bound (N M L KR KG KV l₁ l₂ : ℝ) (m : ℕ) (hN : 0 ≤ N) (hKR : 0 ≤ KR)
    (hKG : 0 ≤ KG) (hKV : 0 ≤ KV) (hL : 2 ≤ L)
    (hM : M = 2 * KR * L + KG * L ^ 2 + m) (hl₁ : l₁ ≤ 2 * L) (hl₂ : l₂ ≤ 2 * L) :
    (2 * (2 * (N * M)) + KV * N * (1 + l₁ + l₂)) / (2 * Real.pi) ≤
      (4 * (2 * KR + KG + m) + 5 * KV) * N * L ^ 2 := by
  have hpi : 4 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have h1L : 1 ≤ L ^ 2 := by nlinarith
  have hMb : M ≤ (2 * KR + KG + m) * L ^ 2 := by
    rw [hM]
    have h1 : 2 * KR * L ≤ 2 * KR * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (by positivity)
    have h2 : (m : ℝ) ≤ m * L ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    nlinarith
  have hl : 1 + l₁ + l₂ ≤ 5 * L ^ 2 := by nlinarith
  have hNM : N * M ≤ N * ((2 * KR + KG + m) * L ^ 2) := mul_le_mul_of_nonneg_left hMb hN
  have hNV : KV * N * (1 + l₁ + l₂) ≤ KV * N * (5 * L ^ 2) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  have hnum : 2 * (2 * (N * M)) + KV * N * (1 + l₁ + l₂) ≤
      (4 * (2 * KR + KG + m) + 5 * KV) * N * L ^ 2 := by nlinarith
  have h0 : 0 ≤ (4 * (2 * KR + KG + m) + 5 * KV) * N * L ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  nlinarith

open Complex in
/-- **The rectangle estimate.** -/
private lemma rectangle_estimate (F G H : ℂ → ℂ) (m : ℕ) (D : FunctionalEquation F) (Λ : ℕ → ℂ)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Complex.Gamma (D.α i * s + D.r i)) * G s)
    (hHrefl : ∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s))
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) (hfinH : ∀ p, analyticOrderAt H p ≠ ⊤)
    (KG : ℝ) (hKG0 : 0 ≤ KG)
    (KV : ℝ) (hKV0 : 0 ≤ KV)
    (hvert : ∀ n : ℕ, 2 ≤ n → ∀ A B : ℝ, A ≤ 0 → 0 ≤ B →
      ‖(I • (∫ y : ℝ in A..B, deriv H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in A..B, deriv H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) -
        I * (-(((B - A : ℝ) : ℂ) * Λ n))‖ ≤
        KV * (n : ℝ) ^ (3 / 2 : ℝ) * (1 + Real.log (1 + |A|) + Real.log (1 + B)))
    (KR : ℝ) (hKR0 : 0 ≤ KR)
    (hRb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖(m : ℂ) / s + Complex.log D.Q + (∑ i, (D.α i : ℂ) * digamma (D.α i * s + D.r i)) +
        (m : ℂ) / (s - 1)‖ ≤ KR * Real.log |s.im|)
    (T : ℝ) (hT8 : 8 ≤ T) (T₁ T₂ : ℝ) (hT₁a : T < T₁) (hT₁b : T₁ < T + 1) (hT₂a : T < T₂)
    (hT₂b : T₂ < T + 1)
    (hT₁g : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 → G (u + (1 : ℝ) * T₁ * I) ≠ 0 ∧
      ‖deriv G (u + (1 : ℝ) * T₁ * I) / G (u + (1 : ℝ) * T₁ * I)‖ ≤ KG * Real.log T ^ 2)
    (hT₂g : ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 → G (u + (-1 : ℝ) * T₂ * I) ≠ 0 ∧
      ‖deriv G (u + (-1 : ℝ) * T₂ * I) / G (u + (-1 : ℝ) * T₂ * I)‖ ≤ KG * Real.log T ^ 2)
    (Z : Finset ℂ) (hZ : ∀ ρ, ρ ∈ Z ↔ H ρ = 0 ∧ -T₂ < ρ.im ∧ ρ.im < T₁) (n : ℕ) (hn : 2 ≤ n) :
    ‖(∑ ρ ∈ Z, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ) +
      (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n‖ ≤
      (4 * (2 * KR + KG + m) + 5 * KV) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hl8 : 2 < Real.log 8 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  have hlT : 2 ≤ Real.log T := le_trans hl8.le (Real.log_le_log (by norm_num) hT8)
  set M : ℝ := 2 * KR * Real.log T + KG * Real.log T ^ 2 + m with hM
  have hTop := norm_logDeriv_horizontal_le F G H m D hFd hGF hHd hHr hHrefl KR hKR0 hRb KG T hT8 1
      (Or.inl rfl)
    T₁ hT₁a hT₁b hT₁g
  have hBot := norm_logDeriv_horizontal_le F G H m D hFd hGF hHd hHr hHrefl KR hKR0 hRb KG T hT8
      (-1) (Or.inr rfl)
    T₂ hT₂a hT₂b hT₂g
  simp only [one_mul, neg_one_mul] at hTop hBot
  have hZin : ∀ p ∈ Z, (-1 / 2 : ℝ) < p.re ∧ p.re < (3 / 2 : ℝ) ∧ -T₂ < p.im ∧ p.im < T₁ := by
    intro p hp
    obtain ⟨h0, h1, h2⟩ := (hZ p).1 hp
    obtain ⟨r0, r1⟩ := hstrip p h0
    exact ⟨by linarith, by linarith, h1, h2⟩
  have hZ2 : ∀ s : ℂ, (-1 / 2 : ℝ) ≤ s.re → s.re ≤ (3 / 2 : ℝ) → -T₂ ≤ s.im → s.im ≤ T₁ →
      H s = 0 → s ∈ Z := by
    intro s h1 h2 h3 h4 h0
    have hse : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
    refine (hZ s).2 ⟨h0, lt_of_le_of_ne h3 fun h => ?_, lt_of_le_of_ne h4 fun h => ?_⟩
    · have := (hBot s.re h1 h2).1
      rw [h, ← hse] at this; exact this h0
    · have := (hTop s.re h1 h2).1
      rw [h.symm, ← hse] at this; exact this h0
  have hres := boundaryIntegral_logDeriv_mul_cpow H hHd n hn0 (-1 / 2) (3 / 2) (-T₂) T₁ Z hZin hZ2
      hfinH
    (by norm_num) (by linarith)
  have hSx : ∑ p ∈ Z, (analyticOrderNatAt H p : ℂ) * ((n : ℝ) : ℂ) ^ p =
      ∑ ρ ∈ Z, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ := by
    simp only [Complex.ofReal_natCast]
  rw [hSx] at hres
  have hV := hvert n hn (-T₂) T₁ (by linarith) (by linarith)
  have hTopI := norm_horizontal_segment_le (fun z => deriv H z / H z) n T₁ M hn1 fun u h1 h2 =>
      (hTop u h1 h2).2
  have hBotI := norm_horizontal_segment_le (fun z => deriv H z / H z) n (-T₂) M hn1 fun u h1 h2 =>
    (hBot u h1 h2).2
  have halg := zero_sum_eq_of_contour hres hV hBotI hTopI
  refine halg.trans ?_
  have hlogT1 : Real.log (1 + T₁) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  have hlogT2 : Real.log (1 + |-T₂|) ≤ 2 * Real.log T := by
    rw [abs_neg, abs_of_pos (by linarith), ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
  exact rectangle_real_bound _ M (Real.log T) KR KG KV _ _ m (by positivity) hKR0 hKG0 hKV0 hlT hM
    hlogT2 hlogT1

/-- The zeros of `H` near `±T` lie in a set of total multiplicity `≤ 2 K log T`. -/
private lemma card_zeros_near_height_le (G H : ℂ → ℂ) (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1)
    (TX : ℝ) (hHG : ∀ ρ, H ρ = 0 → TX < |ρ.im| →
      G ρ = 0 ∧ analyticOrderNatAt H ρ = analyticOrderNatAt G ρ)
    (KG T : ℝ) (hTX : TX + 1 ≤ T) (Zp Zm : Finset ℂ)
    (hZp2 : ∀ ρ, G ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → T ≤ (1 : ℝ) * ρ.im → (1 : ℝ) * ρ.im ≤ T + 1 →
      ρ ∈ Zp)
    (hZp3 : (∑ ρ ∈ Zp, (analyticOrderNatAt G ρ : ℝ)) ≤ KG * Real.log T)
    (hZm2 : ∀ ρ, G ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → T ≤ (-1 : ℝ) * ρ.im → (-1 : ℝ) * ρ.im ≤ T + 1 →
      ρ ∈ Zm)
    (hZm3 : (∑ ρ ∈ Zm, (analyticOrderNatAt G ρ : ℝ)) ≤ KG * Real.log T) :
    ∃ W : Finset ℂ, (∀ ρ, H ρ = 0 → T < |ρ.im| → |ρ.im| < T + 1 → ρ ∈ W) ∧
      (∑ ρ ∈ W, (analyticOrderNatAt H ρ : ℝ)) ≤ 2 * KG * Real.log T := by
  classical
  set W : Finset ℂ := (Zp ∪ Zm).filter (fun ρ => H ρ = 0 ∧ TX < |ρ.im|) with hW
  refine ⟨W, fun ρ h0 h1 h2 => ?_, ?_⟩
  · have hTρ : TX < |ρ.im| := by linarith
    obtain ⟨hG0, -⟩ := hHG ρ h0 hTρ
    obtain ⟨hr0, hr1⟩ := hstrip ρ h0
    simp only [W, Finset.mem_filter, Finset.mem_union]
    refine ⟨?_, h0, hTρ⟩
    rcases le_or_gt 0 ρ.im with hi | hi
    · rw [abs_of_nonneg hi] at h1 h2
      left; exact hZp2 ρ hG0 hr0 hr1 (by linarith) (by linarith)
    · rw [abs_of_neg hi] at h1 h2
      right; exact hZm2 ρ hG0 hr0 hr1 (by linarith) (by linarith)
  · have hle : ∑ ρ ∈ W, (analyticOrderNatAt H ρ : ℝ) ≤
        ∑ ρ ∈ Zp ∪ Zm, (analyticOrderNatAt G ρ : ℝ) := by
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ hρ => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Nat.cast_nonneg _)
      simp only [W, Finset.mem_filter] at hρ
      rw [(hHG ρ hρ.2.1 hρ.2.2).2]
    have hu : ∑ ρ ∈ Zp ∪ Zm, (analyticOrderNatAt G ρ : ℝ) ≤
        ∑ ρ ∈ Zp, (analyticOrderNatAt G ρ : ℝ) + ∑ ρ ∈ Zm, (analyticOrderNatAt G ρ : ℝ) := by
      rw [← Finset.sum_union_inter]
      have : 0 ≤ ∑ ρ ∈ Zp ∩ Zm, (analyticOrderNatAt G ρ : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      linarith
    linarith

open Complex in
/-- **Bookkeeping at a large height.** From the rectangle estimate to the zero sum over
`|Im ρ| ≤ T`. -/
private lemma zero_sum_bound_of_rectangle (F H : ℂ → ℂ) (Λ : ℕ → ℂ) (X : Finset ℂ) (n : ℕ) (hn : 2
    ≤ n)
    (T T₁ T₂ : ℝ) (hT₁a : T < T₁) (hT₁b : T₁ < T + 1) (hT₂a : T < T₂) (hT₂b : T₂ < T + 1)
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) (hXre : ∀ x ∈ X, x.re ≤ 1)
    (heqFH : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ∉ X →
      ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ))
    (hfinF : {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite)
    (hfinH : {ρ | H ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite)
    (W : Finset ℂ) (hW : ∀ ρ, H ρ = 0 → T < |ρ.im| → |ρ.im| < T + 1 → ρ ∈ W) (NW : ℝ)
    (hNW : (∑ ρ ∈ W, (analyticOrderNatAt H ρ : ℝ)) ≤ NW)
    (Z : Finset ℂ) (hZ : ∀ ρ, ρ ∈ Z ↔ H ρ = 0 ∧ -T₂ < ρ.im ∧ ρ.im < T₁) (E : ℝ)
    (hE : ‖(∑ ρ ∈ Z, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ) +
      (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n‖ ≤ E) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) + T / Real.pi * Λ n‖ ≤
      (∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x)) * n + NW * n + E +
        ‖Λ n‖ := by
  classical
  have hn1 : 1 ≤ n := by omega
  set S : Set ℂ := {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T} with hSdef
  have hset : {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T} = {ρ | F ρ = 0 ∧ ρ ∈ S} := rfl
  rw [hset]
  have h1 := finsum_zeros_eq_of_eqOn_compl F H (fun ρ => (n : ℂ) ^ ρ) X S n hfinF hfinH
    (fun ρ hρ hX => heqFH ρ hρ.1 hX) (fun x hx => Complex.norm_natCast_cpow_le_self hn1 (hXre x hx))
  set SF := ∑ᶠ ρ ∈ {ρ | F ρ = 0 ∧ ρ ∈ S}, (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ
  set SH := ∑ᶠ ρ ∈ {ρ | H ρ = 0 ∧ ρ ∈ S}, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ with hSH
  set SZ := ∑ ρ ∈ Z, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ with hSZ
  -- `SZ - SH` is a sum over the zeros near `±T`
  set A := hfinH.toFinset with hA
  have hSHA : SH = ∑ ρ ∈ A, (analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ :=
    finsum_mem_eq_finite_toFinset_sum _ hfinH
  have hAZ : A ⊆ Z := by
    intro ρ hρ
    rw [hA, Set.Finite.mem_toFinset] at hρ
    obtain ⟨h0, -, h2⟩ := hρ
    have := abs_le.1 h2
    exact (hZ ρ).2 ⟨h0, by linarith, by linarith⟩
  have h2 : ‖SZ - SH‖ ≤ NW * n := by
    rw [hSHA, hSZ, ← Finset.sum_sdiff hAZ, add_sub_cancel_right]
    refine (norm_sum_le _ _).trans ?_
    have hsub : Z \ A ⊆ W := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      obtain ⟨h0, h1, h2⟩ := (hZ ρ).1 hρ.1
      have hnot : ¬ (0 ≤ ρ.re ∧ |ρ.im| ≤ T) := fun h =>
        hρ.2 (by rw [hA, Set.Finite.mem_toFinset]; exact ⟨h0, h⟩)
      have hre := (hstrip ρ h0).1
      have hT : T < |ρ.im| := by
        by_contra h; push Not at h; exact hnot ⟨hre, h⟩
      have hT1 : |ρ.im| < T + 1 := by rw [abs_lt]; constructor <;> linarith
      exact hW ρ h0 hT hT1
    calc ∑ ρ ∈ Z \ A, ‖(analyticOrderNatAt H ρ : ℂ) * (n : ℂ) ^ ρ‖
        ≤ ∑ ρ ∈ Z \ A, (analyticOrderNatAt H ρ : ℝ) * n := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul, Complex.norm_natCast]
          have h0 := ((hZ ρ).1 (Finset.mem_sdiff.1 hρ).1).1
          exact mul_le_mul_of_nonneg_left (Complex.norm_natCast_cpow_le_self hn1 (hstrip ρ h0).2)
              (Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ W, (analyticOrderNatAt H ρ : ℝ) * n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (∑ ρ ∈ W, (analyticOrderNatAt H ρ : ℝ)) * n := by rw [Finset.sum_mul]
      _ ≤ NW * n := by gcongr
  -- the main term
  have h4 : ‖((T / Real.pi : ℝ) : ℂ) * Λ n - (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n‖ ≤
      ‖Λ n‖ := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hpi := Real.pi_pos
    have e : T / Real.pi - (T₁ + T₂) / (2 * Real.pi) = (2 * T - T₁ - T₂) / (2 * Real.pi) := by
      field_simp; ring
    rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    have h3 : |2 * T - T₁ - T₂| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have h5 : |2 * T - T₁ - T₂| / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    calc |2 * T - T₁ - T₂| / (2 * Real.pi) * ‖Λ n‖ ≤ 1 * ‖Λ n‖ := by gcongr
      _ = ‖Λ n‖ := one_mul _
  have e : SF + T / Real.pi * Λ n = (SF - SH) - (SZ - SH) +
      (SZ + (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n) +
      (((T / Real.pi : ℝ) : ℂ) * Λ n - (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n) := by
    push_cast; ring
  rw [e]
  calc _ ≤ ‖SF - SH‖ + ‖SZ - SH‖ + ‖SZ + (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n‖ +
        ‖((T / Real.pi : ℝ) : ℂ) * Λ n - (((T₁ + T₂) / (2 * Real.pi) : ℝ) : ℂ) * Λ n‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr
        refine (norm_add_le _ _).trans ?_; gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by gcongr

open Complex in
/-- **Large heights.** -/
private lemma zero_sum_bound_large (F G H : ℂ → ℂ) (m : ℕ) (D : FunctionalEquation F) (Λ : ℕ → ℂ)
    (hFd : DifferentiableOn ℂ F {1}ᶜ) (hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s)
    (hHd : Differentiable ℂ H)
    (hHr : ∀ s : ℂ, 0 < s.re → H s = s ^ m * (D.Q : ℂ) ^ s *
        (∏ i, Complex.Gamma (D.α i * s + D.r i)) * G s)
    (hHrefl : ∀ s, H (1 - starRingEnd ℂ s) = D.w * starRingEnd ℂ (H s))
    (hstrip : ∀ s, H s = 0 → 0 ≤ s.re ∧ s.re ≤ 1) (hfinH : ∀ p, analyticOrderAt H p ≠ ⊤)
    (KG : ℝ) (hKG0 : 0 ≤ KG)
    (hgood : ∀ T : ℝ, 8 ≤ T → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      (∃ Z : Finset ℂ, (∀ ρ ∈ Z, G ρ = 0) ∧
        (∀ ρ, G ρ = 0 → 0 ≤ ρ.re → ρ.re ≤ 1 → T ≤ ε * ρ.im → ε * ρ.im ≤ T + 1 → ρ ∈ Z) ∧
        (∑ ρ ∈ Z, (analyticOrderNatAt G ρ : ℝ)) ≤ KG * Real.log T) ∧
      ∃ T' : ℝ, T < T' ∧ T' < T + 1 ∧ ∀ u : ℝ, 1 / 2 ≤ u → u ≤ 3 / 2 →
        G (u + ε * T' * I) ≠ 0 ∧
        ‖deriv G (u + ε * T' * I) / G (u + ε * T' * I)‖ ≤ KG * Real.log T ^ 2)
    (KV : ℝ) (hKV0 : 0 ≤ KV)
    (hvert : ∀ n : ℕ, 2 ≤ n → ∀ A B : ℝ, A ≤ 0 → 0 ≤ B →
      ‖(I • (∫ y : ℝ in A..B, deriv H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I • (∫ y : ℝ in A..B, deriv H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) /
            H (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) *
            ((n : ℝ) : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))) -
        I * (-(((B - A : ℝ) : ℂ) * Λ n))‖ ≤
        KV * (n : ℝ) ^ (3 / 2 : ℝ) * (1 + Real.log (1 + |A|) + Real.log (1 + B)))
    (KR : ℝ) (hKR0 : 0 ≤ KR)
    (hRb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖(m : ℂ) / s + Complex.log D.Q + (∑ i, (D.α i : ℂ) * digamma (D.α i * s + D.r i)) +
        (m : ℂ) / (s - 1)‖ ≤ KR * Real.log |s.im|)
    (X : Finset ℂ) (TX : ℝ) (hXre : ∀ x ∈ X, x.re ≤ 1)
    (heqFH : ∀ ρ : ℂ, 0 ≤ ρ.re → ρ ∉ X →
      ((F ρ = 0 ↔ H ρ = 0) ∧ analyticOrderNatAt F ρ = analyticOrderNatAt H ρ))
    (hHG : ∀ ρ, H ρ = 0 → TX < |ρ.im| →
      G ρ = 0 ∧ analyticOrderNatAt H ρ = analyticOrderNatAt G ρ)
    (hfinHS : ∀ T : ℝ, {ρ | H ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite)
    (hfinFS : ∀ T : ℝ, {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite)
    (hfinHT : ∀ T : ℝ, {ρ | H ρ = 0 ∧ |ρ.im| ≤ T}.Finite)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hΛn : ∀ n : ℕ, 2 ≤ n → ‖Λ n‖ ≤ C₁ * (n : ℝ) ^ (3 / 2 : ℝ)) :
    ∀ n : ℕ, 2 ≤ n → ∀ T : ℝ, max 8 (TX + 1) ≤ T →
      ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) + T / Real.pi * Λ n‖ ≤
        ((∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x)) + 2 * KG + C₁ +
          (4 * (2 * KR + KG + m) + 5 * KV)) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
  classical
  intro n hn2 T hTT
  have hT8 : 8 ≤ T := le_trans (le_max_left _ _) hTT
  have hTX : TX + 1 ≤ T := le_trans (le_max_right _ _) hTT
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  obtain ⟨⟨Zp, -, hZp2, hZp3⟩, T₁, hT₁a, hT₁b, hT₁g⟩ := hgood T hT8 1 (Or.inl rfl)
  obtain ⟨⟨Zm, -, hZm2, hZm3⟩, T₂, hT₂a, hT₂b, hT₂g⟩ := hgood T hT8 (-1) (Or.inr rfl)
  obtain ⟨W, hW, hNW⟩ := card_zeros_near_height_le G H hstrip TX hHG KG T hTX Zp Zm hZp2 hZp3 hZm2
      hZm3
  set Z : Finset ℂ := (hfinHT (T + 1)).toFinset.filter (fun ρ => -T₂ < ρ.im ∧ ρ.im < T₁)
    with hZdef
  have hZ : ∀ ρ, ρ ∈ Z ↔ H ρ = 0 ∧ -T₂ < ρ.im ∧ ρ.im < T₁ := by
    intro ρ
    simp only [Z, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h0, -⟩, h1, h2⟩; exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by rw [abs_le]; constructor <;> linarith⟩, h1, h2⟩
  have hE := rectangle_estimate F G H m D Λ hFd hGF hHd hHr hHrefl hstrip hfinH KG hKG0 KV hKV0
    hvert KR hKR0 hRb T hT8 T₁ T₂ hT₁a hT₁b hT₂a hT₂b hT₁g hT₂g Z hZ n hn2
  have hmain := zero_sum_bound_of_rectangle F H Λ X n hn2 T T₁ T₂ hT₁a hT₁b hT₂a hT₂b hstrip hXre
      heqFH
    (hfinFS T) (hfinHS T) W hW _ hNW Z hZ _ hE
  refine hmain.trans ?_
  set CX := ∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x) with hCX
  have hCX0 : 0 ≤ CX := Finset.sum_nonneg fun _ _ => by positivity
  set KE := 4 * (2 * KR + KG + m) + 5 * KV with hKE
  set N := (n : ℝ) ^ (3 / 2 : ℝ) with hNdef
  set L := Real.log T with hL
  have hN : (n : ℝ) ≤ N := by
    rw [hNdef]
    conv_lhs => rw [← Real.rpow_one (n : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hN0 : 0 ≤ N := by positivity
  have hlT : 1 ≤ L := by
    have : Real.log 8 ≤ Real.log T := Real.log_le_log (by norm_num) hT8
    have h8 : 1 < Real.log 8 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h1L : 1 ≤ L ^ 2 := by nlinarith
  have hA1 : CX * n ≤ CX * N * L ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hN hCX0
    have h2 : CX * N ≤ CX * N * L ^ 2 := le_mul_of_one_le_right (by positivity) h1L
    linarith
  have hA2 : 2 * KG * L * n ≤ 2 * KG * N * L ^ 2 := by
    have h0 : 0 ≤ 2 * KG := by positivity
    have h1 : 2 * KG * L * n ≤ 2 * KG * L ^ 2 * N :=
      mul_le_mul (mul_le_mul_of_nonneg_left hLL h0) hN hn0.le (by positivity)
    linarith
  have hA3 : ‖Λ n‖ ≤ C₁ * N * L ^ 2 := by
    refine (hΛn n hn2).trans ?_
    exact le_mul_of_one_le_right (by positivity) h1L
  have e : (CX + 2 * KG + C₁ + KE) * N * L ^ 2 =
      CX * N * L ^ 2 + 2 * KG * N * L ^ 2 + KE * N * L ^ 2 + C₁ * N * L ^ 2 := by ring
  rw [e]
  linarith

/-- **Small heights.** -/
private lemma zero_sum_bound_small (F : ℂ → ℂ) (Λ : ℕ → ℂ)
    (hfinFS : ∀ T : ℝ, {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}}.Finite)
    (hFre : ∀ ρ, F ρ = 0 → ρ.re ≤ 1)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hΛn : ∀ n : ℕ, 2 ≤ n → ‖Λ n‖ ≤ C₁ * (n : ℝ) ^ (3 / 2 : ℝ))
    (T₀ : ℝ) (hT₀ : 2 ≤ T₀) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ T : ℝ, 2 ≤ T → T < T₀ →
      ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) + T / Real.pi * Λ n‖ ≤
        4 * (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
  classical
  set K₀ : ℝ := ∑ ρ ∈ (hfinFS T₀).toFinset, (analyticOrderNatAt F ρ : ℝ) with hK₀
  have hK₀0 : 0 ≤ K₀ := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨K₀, hK₀0, fun n hn2 T hT hTT => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hN : (n : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (n : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hN0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hsub : {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}} ⊆
      {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T₀}} := fun ρ hρ =>
    ⟨hρ.1, hρ.2.1, le_trans hρ.2.2 hTT.le⟩
  have hset : {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T} =
      {ρ | F ρ = 0 ∧ ρ ∈ {ρ : ℂ | 0 ≤ ρ.re ∧ |ρ.im| ≤ T}} := rfl
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ (hfinFS T)]
  have hS : ‖∑ ρ ∈ (hfinFS T).toFinset, (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ‖ ≤
      K₀ * n := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ρ ∈ (hfinFS T).toFinset, ‖(analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ‖
        ≤ ∑ ρ ∈ (hfinFS T).toFinset, (analyticOrderNatAt F ρ : ℝ) * n := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul, Complex.norm_natCast]
          rw [Set.Finite.mem_toFinset] at hρ
          exact mul_le_mul_of_nonneg_left (Complex.norm_natCast_cpow_le_self (by omega) (hFre ρ
              hρ.1))
            (Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ (hfinFS T₀).toFinset, (analyticOrderNatAt F ρ : ℝ) * n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Set.Finite.toFinset_subset_toFinset.2 hsub) fun _ _ _ => by positivity
      _ = K₀ * n := by rw [hK₀, Finset.sum_mul]
  have hTΛ : ‖(T : ℂ) / (Real.pi : ℂ) * Λ n‖ ≤ T₀ * C₁ * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [norm_mul]
    have hTpi : ‖(T : ℂ) / (Real.pi : ℂ)‖ ≤ T₀ := by
      rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith), abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    calc ‖(T : ℂ) / (Real.pi : ℂ)‖ * ‖Λ n‖ ≤ T₀ * (C₁ * (n : ℝ) ^ (3 / 2 : ℝ)) :=
          mul_le_mul hTpi (hΛn n hn2) (norm_nonneg _) (by linarith)
      _ = T₀ * C₁ * (n : ℝ) ^ (3 / 2 : ℝ) := by ring
  have hK₀n : K₀ * n ≤ K₀ * (n : ℝ) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hN hK₀0
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlT2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hLsq : 1 / 4 ≤ Real.log T ^ 2 := by nlinarith
  have hfin : (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) ≤
      4 * (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
    have h0 : 0 ≤ (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
    nlinarith
  calc _ ≤ ‖∑ ρ ∈ (hfinFS T).toFinset, (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ‖ +
        ‖(T : ℂ) / (Real.pi : ℂ) * Λ n‖ := norm_add_le _ _
    _ ≤ K₀ * n + T₀ * C₁ * (n : ℝ) ^ (3 / 2 : ℝ) := add_le_add hS hTΛ
    _ ≤ _ := by nlinarith

/-- **Landau's formula for the Selberg class.** Let `a ∈ 𝒮` with continuation `F`, and let
`-F'/F = ∑ Λ n n^{-s}` on `Re s > 1`. Then, uniformly in `n > 1` and `T ≥ 2`,
`∑_{|γ| ≤ T} m_ρ n^ρ = -(T/π) Λ(n) + O(n^{3/2} log² T)`, the sum running over the zeros
`ρ = β + iγ` of `F` with `β ≥ 0`, counted with multiplicity `m_ρ`. -/
theorem exists_norm_finsum_zeros_cpow_add_le (a : ArithmeticFunction ℂ) (ha : a ∈ selbergClass) (F
    : ℂ → ℂ)
    (hF : IsLSeriesContinuation a F) (Λ : ℕ → ℂ)
    (hΛ : ∀ s : ℂ, 1 < s.re → LSeriesHasSum Λ s (-deriv F s / F s)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 < n → ∀ T : ℝ, 2 ≤ T →
      ‖(∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
          (analyticOrderNatAt F ρ : ℂ) * (n : ℂ) ^ ρ) + T / Real.pi * Λ n‖ ≤
        C * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
  classical
  obtain ⟨-, ⟨F₀, hF₀, ⟨m, G, β, hGd, hGo, hGF₀⟩, ⟨D₀⟩⟩, ⟨b, θ, hθ, hlog, Cb, hbC⟩, hram⟩ := ha
  have hFF₀ : ∀ s, s ≠ 1 → F s = F₀ s := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have h3 : F =ᶠ[nhds (2 : ℂ)] F₀ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
      rw [hF.1 s hs, hF₀.1 s hs]
    intro s hs
    exact (hF.2.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      (hF₀.2.analyticOnNhd hU) hpc (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) h3 hs
  have hGF : ∀ s, s ≠ 1 → G s = (s - 1) ^ m * F s := fun s hs => by
    rw [hFF₀ s hs]; exact hGF₀ s hs
  obtain ⟨D⟩ : Nonempty (FunctionalEquation F) := ⟨D₀.congr hFF₀⟩
  obtain ⟨Ca, hCa⟩ := hram (1 / 2) (by norm_num)
  obtain ⟨B2, hB20, hB2⟩ := norm_le_of_two_le_re a F hF Ca hCa
  obtain ⟨κ, hκ, hκF⟩ := exists_le_norm_of_re_eq_two a F hF b hlog
  obtain ⟨Ag, Cg, hAg, hgrow⟩ := exists_norm_le_mul_rpow_strip F G m β hGd hGo hGF hF.2 D B2 hB20
      hB2 7 (by norm_num)
  have hlowG : ∀ s : ℂ, s.re = 2 → 1 ≤ |s.im| → κ ≤ ‖G s‖ := by
    intro s hs _
    have hs1 : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [hGF s hs1, norm_mul, norm_pow]
    have h1 : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hs, Complex.one_re] at this; norm_num at this; exact this
    calc κ ≤ ‖F s‖ := hκF s hs
      _ ≤ ‖s - 1‖ ^ m * ‖F s‖ := le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ h1)
  obtain ⟨KG, hKG0, hgood⟩ := exists_good_height hGd hAg hκ hgrow hlowG
  obtain ⟨H, hHd, hHrefl, hHr⟩ := exists_completed F G m hGd hGF D
  have hFne1 : ∀ s : ℂ, 1 < s.re → F s ≠ 0 := by
    intro s hs
    rw [hF.1 s hs, (hlog.2 s hs).2]
    exact Complex.exp_ne_zero _
  obtain ⟨hstrip, hH2⟩ := completed_zeros_mem_strip F G H m D hGF hHr hHrefl hFne1
  have hfinH : ∀ p, analyticOrderAt H p ≠ ⊤ := Complex.analyticOrderAt_ne_top_of_differentiable hHd
      hH2
  have hΛeq := eq_logMul_of_neg_logDeriv a F hF b hlog Λ hΛ
  obtain ⟨θ₁, C₁, hθ₁, hC₁, hΛb⟩ := norm_logMul_le_rpow b θ Cb hθ hbC Λ hΛeq
  obtain ⟨KV, hKV0, hvert⟩ := vertical_sides_eq F G H m hF.2 hGF D hHd hHr hHrefl hFne1 Λ hΛ θ₁ C₁
    hθ₁ hC₁ hΛb
  obtain ⟨KR, hKR0, hRb⟩ := norm_archimedean_le_log m D.Q D.α D.r D.α_pos D.r_re_nonneg
  obtain ⟨X, TX, hTX0, hXre, heqFH, hHG⟩ := exists_finset_completed_zeros_eq F G H m D hF.2 hGd hGF
      hHd hHr hstrip
  obtain ⟨hfinHS, hfinFS, hfinHT⟩ := finite_zeros_of_completed F H X hHd hH2 hstrip heqFH
  have hFre : ∀ ρ, F ρ = 0 → ρ.re ≤ 1 := fun ρ h0 => by
    by_contra h; push Not at h; exact hFne1 ρ h h0
  have hΛn : ∀ n : ℕ, 2 ≤ n → ‖Λ n‖ ≤ C₁ * (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    refine (hΛb n (by omega)).trans (mul_le_mul_of_nonneg_left ?_ hC₁)
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hlarge := zero_sum_bound_large F G H m D Λ hF.2 hGF hHd hHr hHrefl hstrip hfinH KG hKG0 hgood
    KV hKV0 hvert KR hKR0 hRb X TX hXre heqFH hHG hfinHS hfinFS hfinHT C₁ hC₁ hΛn
  set T₀ : ℝ := max 8 (TX + 1) with hT₀
  obtain ⟨K₀, hK₀0, hsmall⟩ := zero_sum_bound_small F Λ hfinFS hFre C₁ hC₁ hΛn T₀
    (le_trans (by norm_num) (le_max_left _ _))
  set CL : ℝ := (∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x)) + 2 * KG + C₁ +
    (4 * (2 * KR + KG + m) + 5 * KV) with hCL
  have hCL0 : 0 ≤ CL := by
    have : 0 ≤ ∑ x ∈ X, ((analyticOrderNatAt F x : ℝ) + analyticOrderNatAt H x) :=
      Finset.sum_nonneg fun _ _ => by positivity
    positivity
  refine ⟨CL + 4 * (K₀ + T₀ * C₁), fun n hn T hT => ?_⟩
  have hn2 : 2 ≤ n := hn
  have hN0 : 0 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hpos1 : 0 ≤ CL * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by positivity
  have hpos2 : 0 ≤ 4 * (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by
    have : 0 ≤ T₀ := le_trans (by norm_num) (le_max_left _ _)
    positivity
  have e : (CL + 4 * (K₀ + T₀ * C₁)) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 =
      CL * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 +
        4 * (K₀ + T₀ * C₁) * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 := by ring
  rw [e]
  rcases le_or_gt T₀ T with hTT | hTT
  · have := hlarge n hn2 T hTT
    linarith
  · have := hsmall n hn2 T hT hTT
    linarith

end SelbergClass
