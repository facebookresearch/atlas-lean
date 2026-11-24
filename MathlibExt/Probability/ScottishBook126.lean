/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import MathlibExt.Probability.CharFunTaylorBounds

/-!
# Kac's Scottish Book Problem 126

The normalized characteristic-function powers tend to zero for a mean-zero integrable
function on the unit interval with infinite second moment.
-/

public section

namespace MathlibExt.Probability.ScottishBook126Wanted

open MeasureTheory Filter
open scoped Topology

-- The half-angle identity expresses the rescaled cosine deficit using the continuous sinc.
private lemma tendsto_cos_deficit (a : ℝ) :
    Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) * (1 - Real.cos (a / √(n : ℝ))))
      atTop (𝓝 (a ^ 2)) := by
  have ht : Tendsto (fun n : ℕ ↦ a / √(n : ℝ) / 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) (a := a)).div_const 2
  have hs := (Real.continuous_sinc.tendsto 0).comp ht
  have hlim : Tendsto (fun n : ℕ ↦ a ^ 2 * Real.sinc (a / √(n : ℝ) / 2) ^ 2)
      atTop (𝓝 (a ^ 2)) := by
    simpa using (hs.pow 2).const_mul (a ^ 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  let u := a / √(n : ℝ) / 2
  have hsin : u * Real.sinc u = Real.sin u := by
    by_cases hu : u = 0
    · simp [hu]
    · rw [Real.sinc_of_ne_zero hu]
      field_simp
  have hcos := Real.sin_sq_eq_half_sub u
  rw [show 2 * u = a / √(n : ℝ) by dsimp [u]; ring, ← hsin, mul_pow] at hcos
  have hn' : 0 < √(n : ℝ) := by positivity
  have hau : a = 2 * √(n : ℝ) * u := by dsimp [u]; field_simp
  change a ^ 2 * Real.sinc u ^ 2 = _
  calc
    _ = 4 * (n : ℝ) * (u ^ 2 * Real.sinc u ^ 2) := by
      conv_lhs => lhs; rw [hau]
      simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    _ = _ := by rw [hcos]; ring

-- Fatou's lemma converts the infinite second moment into divergence of the integrals.
private lemma tendsto_integral_cos_deficit {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (hinf : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ = ⊤) :
    Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) * ∫ x, (1 - Real.cos (f x / √(n : ℝ))) ∂μ)
      atTop atTop := by
  let g (n : ℕ) (x : ℝ) := 2 * (n : ℝ) * (1 - Real.cos (f x / √(n : ℝ)))
  have hfatou := lintegral_liminf_le (μ := μ) (f := fun n x ↦ ENNReal.ofReal (g n x))
    (fun n ↦ by dsimp [g]; fun_prop) (u := atTop)
  have hpoint (x : ℝ) : liminf (fun n ↦ ENNReal.ofReal (g n x)) atTop =
      ENNReal.ofReal (f x ^ 2) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_cos_deficit (f x))).liminf_eq
  simp_rw [hpoint, hinf] at hfatou
  have hlim := tendsto_of_le_liminf_of_limsup_le hfatou le_top
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  apply hlim.congr
  intro n
  have hcos : Integrable (fun x ↦ Real.cos (f x / √(n : ℝ))) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ Real.abs_cos_le_one _)
  have hg : Integrable (g n) μ := ((integrable_const 1).sub hcos).const_mul _
  have hg₀ (x : ℝ) : 0 ≤ g n x :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  rw [← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg₀)]
  simp [g, integral_const_mul]

/--
**Kac's Scottish Book Problem 126.** Let $f : \mathbb{R} \to \mathbb{R}$ be a measurable function
that is integrable on $[0, 1]$ and satisfies $\int_0^1 f(x)\,dx = 0$ and
$\int_0^1 f(x)^2\,dx = \infty$. Then the complex numbers
$\left(\int_0^1 \exp\left(i f(x) / \sqrt{n}\right) dx\right)^n$ tend to $0$ as $n \to \infty$
through the natural numbers.

Source: M. Kac,
Problem 126 of the Scottish Book; solved affirmatively by A. Khintchine,
fourth communique on dependent functions, Studia Mathematicae 6 or 7, as
cited in the typescript addendum Ad 126. The typescript parenthetical
states the finite-variance case as `e ^ (-1 / 2)` where `e ^ (-A / 2)` for
`A = ∫_0^1 f^2` would be expected; that parenthetical is not used here.
-/
theorem khintchine_infinite_variance_limit :
    ∀ f : ℝ → ℝ,
      Measurable f →
      MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) 1) MeasureTheory.volume →
      (∫ x in Set.Icc (0 : ℝ) 1, f x ∂MeasureTheory.volume) = 0 →
      (∫⁻ x in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ((f x) ^ 2) ∂MeasureTheory.volume) = ⊤ →
      Filter.Tendsto
        (fun n : ℕ =>
          (∫ x in Set.Icc (0 : ℝ) 1,
            Complex.exp (Complex.I * (f x : ℂ) / (Real.sqrt (n : ℝ) : ℂ))
              ∂MeasureTheory.volume) ^ n)
        Filter.atTop (nhds (0 : ℂ)) := by
  intro f hf hint _ hsecond
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let z (n : ℕ) := ∫ x, Complex.exp (↑(f x / √(n : ℝ)) * Complex.I) ∂μ
  have hz (n : ℕ) : z n = charFun (μ.map f) (√(n : ℝ))⁻¹ := by
    rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
    simp [z, div_eq_inv_mul]
  have hre (n : ℕ) : 1 - (z n).re = ∫ x, (1 - Real.cos (f x / √(n : ℝ))) ∂μ := by
    have he : Integrable (fun x ↦ Complex.exp (↑(f x / √(n : ℝ)) * Complex.I)) μ :=
      Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ (Complex.norm_exp_ofReal_mul_I _).le)
    have hc := he.re
    change Integrable (fun x ↦ (Complex.exp (↑(f x / √(n : ℝ)) * Complex.I)).re) μ at hc
    simp only [Complex.exp_ofReal_mul_I_re] at hc
    rw [integral_sub (integrable_const 1) hc]
    simp only [integral_const, probReal_univ, one_smul]
    congr 1
    simpa only [z, RCLike.re_eq_complex_re, Complex.exp_ofReal_mul_I_re] using (integral_re he).symm
  have hdiv : Tendsto (fun n : ℕ ↦ 2 * (n : ℝ) * (1 - (z n).re)) atTop atTop := by
    simpa only [hre] using tendsto_integral_cos_deficit (μ := μ) hf hsecond
  let C := ∫ x, |f x| ∂μ
  -- The first absolute moment bounds the error uniformly after scaling by √n.
  have herr (n : ℕ) (hn : 0 < n) : (n : ℝ) * ‖z n - 1‖ ^ 2 ≤ C ^ 2 := by
    have h := CharFunTaylorBounds.norm_charFun_sub_one_le (μ := μ) f hf hint.abs (√(n : ℝ))⁻¹
    rw [← hz, abs_of_nonneg (by positivity), ← div_eq_inv_mul] at h
    have h' := (le_div_iff₀ (by positivity : 0 < √(n : ℝ))).mp h
    have hs := pow_le_pow_left₀ (by positivity) h' 2
    simpa [mul_pow, Real.sq_sqrt, mul_comm, C] using hs
  have hnorm : Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - ‖z n‖)) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [hdiv.eventually_ge_atTop (2 * b + C ^ 2), eventually_gt_atTop 0] with n hb hn
    have hsq : ‖z n - 1‖ ^ 2 = ‖z n‖ ^ 2 - 2 * (z n).re + 1 := by
      simp [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h := herr n hn
    rw [hsq] at h
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (‖z n‖ - 1))]
  have hpow : Tendsto (fun n : ℕ ↦ z n ^ n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hnorm))
    change ‖z n ^ n‖ ≤ Real.exp (-(n * (1 - ‖z n‖)))
    rw [neg_mul_eq_mul_neg, neg_sub, Real.exp_nat_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using Real.add_one_le_exp (‖z n‖ - 1)) n
  simpa only [z, μ, Complex.ofReal_div, mul_comm _ Complex.I, mul_div_assoc] using hpow

end MathlibExt.Probability.ScottishBook126Wanted
