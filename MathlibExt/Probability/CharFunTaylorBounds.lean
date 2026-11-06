/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Taylor bounds for characteristic functions

First- and second-order Taylor bounds for the characteristic function of a
real random variable, and the pointwise exponential estimates they rest on.

## Source

These are the two helper estimates stated (but left unproved) in
`v1/Atlas/TheoryOfProbability/code/LindebergFeller.lean`:
`norm_exp_ofReal_mul_I_sub_one_sub_le` (the pointwise estimate along the
imaginary axis) and `norm_charFun_sub_one_le_sq_mul_variance` (the
characteristic-function bound for a mean-zero, square-integrable variable).
Both are proved here exactly as stated in v1, with no statement correction.
The first-order characteristic-function bound is a new companion, using
Mathlib’s pointwise first-order bound and the same integral argument. Batch 29 (`LindebergFeller.lean`) proved only the qualified
pointwise estimate `‖exp (↑x * I) - 1 - ↑x * I‖ ≤ x ^ 2` under `‖x‖ ≤ 1`
(as `ProbabilityTheory.norm_exp_ofReal_mul_I_sub_one_sub_le`) and did not
port the characteristic-function bound; the unqualified pointwise bound
and the characteristic-function bound below are new.
-/

@[expose] public section

open MeasureTheory Filter Complex

namespace MathlibExt.Probability.CharFunTaylorBounds

/-- **Global second-order bound for the imaginary exponential.** For every real number $u$,
$|e^{iu} - 1 - iu| \le u^2$, with no restriction on the size of $u$.

The proof splits at $u^2 \le 27$: in that range the squared norm is
$(1 - \cos u)^2 + (u - \sin u)^2 \le u^4/4 + u^6/36 \le u^4$, using $1 - \cos u \le u^2/2$ and
$|u - \sin u| \le |u|^3/6$; outside that range $|u| > 5$ and the triangle inequality gives
$2 + |u| \le u^2$. -/
theorem norm_exp_ofReal_mul_I_sub_one_sub_le (u : ℝ) :
    ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖ ≤ u ^ 2 := by
  by_cases h27 : u ^ 2 ≤ 27
  · -- Small-to-moderate `u`: compare squared norms.
    have hexp : Complex.exp (↑u * Complex.I)
        = ↑(Real.cos u) + ↑(Real.sin u) * Complex.I := Complex.exp_ofReal_mul_I u
    have hdiff : Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I
        = ↑(Real.cos u - 1) + ↑(Real.sin u - u) * Complex.I := by
      rw [hexp]
      push_cast
      ring
    have hnorm : ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖
        = Real.sqrt ((Real.cos u - 1) ^ 2 + (Real.sin u - u) ^ 2) := by
      rw [hdiff]
      exact Complex.norm_add_mul_I _ _
    rw [hnorm]
    have hcos : (Real.cos u - 1) ^ 2 ≤ (u ^ 2 / 2) ^ 2 := by
      have h2 : 1 - Real.cos u ≤ u ^ 2 / 2 := by
        have h := Real.one_sub_sq_div_two_le_cos (x := u)
        linarith
      apply sq_le_sq'
      · linarith
      · linarith [Real.cos_le_one u]
    have hsin : (Real.sin u - u) ^ 2 ≤ u ^ 6 / 36 := by
      have h : |Real.sin u - u| ≤ |u| ^ 3 / 6 := by
        have h' := Real.abs_sub_sin_le u
        rwa [abs_sub_comm] at h'
      have h2 : (|u| ^ 3 / 6 : ℝ) ^ 2 = u ^ 6 / 36 := by
        rw [div_pow, show (|u| ^ 3) ^ 2 = (|u| ^ 2) ^ 3 by ring, sq_abs]
        ring
      rw [← h2]
      exact sq_le_sq.mpr (by rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |u| ^ 3 / 6)])
    have hsum : (Real.cos u - 1) ^ 2 + (Real.sin u - u) ^ 2 ≤ u ^ 4 := by
      have h6 : u ^ 6 ≤ 27 * u ^ 4 := by
        have hprod : (0 : ℝ) ≤ u ^ 4 * (27 - u ^ 2) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith [hprod]
      have hcos' : (Real.cos u - 1) ^ 2 ≤ u ^ 4 / 4 := by
        have heq : (u ^ 2 / 2) ^ 2 = u ^ 4 / 4 := by ring
        rwa [heq] at hcos
      have hsin' : (Real.sin u - u) ^ 2 ≤ 3 * u ^ 4 / 4 := by
        have h6' : u ^ 6 / 36 ≤ 3 * u ^ 4 / 4 := by linarith [h6]
        linarith [hsin, h6']
      linarith [hcos', hsin']
    calc Real.sqrt ((Real.cos u - 1) ^ 2 + (Real.sin u - u) ^ 2)
        ≤ Real.sqrt (u ^ 4) := Real.sqrt_le_sqrt hsum
      _ = u ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sqrt_sq (sq_nonneg _)]
  · -- Large `u`: `|u| > 5`, so `2 + |u| ≤ u²` by the triangle inequality.
    have h27' : (27 : ℝ) < u ^ 2 := lt_of_not_ge h27
    have h5 : (5 : ℝ) < |u| := by
      by_contra hle
      have hle' : |u| ≤ 5 := le_of_not_gt hle
      have hle2 : u ^ 2 ≤ 25 := by
        rw [← sq_abs u]
        calc |u| ^ 2 ≤ (5 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle' 2
          _ = 25 := by norm_num
      linarith
    have hnorm_exp : ‖Complex.exp (↑u * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I u
    have htri : ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖ ≤ 2 + |u| := by
      calc ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖
          ≤ ‖Complex.exp (↑u * Complex.I) - 1‖ + ‖(↑u * Complex.I : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ (‖Complex.exp (↑u * Complex.I)‖ + 1) + |u| := by
            have h1 : ‖Complex.exp (↑u * Complex.I) - 1‖
                ≤ ‖Complex.exp (↑u * Complex.I)‖ + 1 := by
              calc ‖Complex.exp (↑u * Complex.I) - 1‖
                  ≤ ‖Complex.exp (↑u * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
                _ = ‖Complex.exp (↑u * Complex.I)‖ + 1 := by simp
            have h2 : ‖(↑u * Complex.I : ℂ)‖ = |u| := by
              rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
                Real.norm_eq_abs]
            rw [h2]
            linarith [h1]
        _ = 2 + |u| := by rw [hnorm_exp]; ring
    calc ‖Complex.exp (↑u * Complex.I) - 1 - ↑u * Complex.I‖
        ≤ 2 + |u| := htri
      _ ≤ u ^ 2 := by
          have hu2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
          nlinarith [hu2, mul_pos (show (0 : ℝ) < |u| - 2 by linarith)
            (show (0 : ℝ) < |u| + 1 by linarith)]

/-- **Second-order Taylor bound for the characteristic function.** Let $X$ be a measurable real
random variable on a probability space with $X^2$ integrable, and let $\varphi_X$ be the
characteristic function of the law of $X$. Then for every real $t$,
$|\varphi_X(t) - 1 - it\,\mathbb{E}[X]| \le t^2 \, \mathbb{E}[X^2]$. -/
theorem norm_charFun_sub_one_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X)
    (hX_sq_int : Integrable (fun ω => (X ω) ^ 2) μ)
    (t : ℝ) :
    ‖charFun (μ.map X) t - 1 - ↑t * Complex.I * ↑(∫ ω, X ω ∂μ)‖
      ≤ t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
  have hX_int : Integrable X μ := by
    have hbound : ∀ ω, |X ω| ≤ ((X ω) ^ 2 + 1) / 2 := by
      intro ω
      have h := two_mul_le_add_sq |X ω| (1 : ℝ)
      rw [sq_abs] at h
      linarith
    have hg_int : Integrable (fun ω => ((X ω) ^ 2 + 1) / 2) μ :=
      (hX_sq_int.add (integrable_const (1 : ℝ))).div_const 2
    exact hg_int.mono' hmeas.aestronglyMeasurable (by
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact hbound ω)
  have hX_ae : AEMeasurable X μ := hmeas.aemeasurable
  -- Integral representation of `charFun (μ.map X) t`.
  have hchar : charFun (μ.map X) t
      = ∫ ω, Complex.exp (↑t * ↑(X ω) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hX_ae
      ((by fun_prop : Measurable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
        ).aestronglyMeasurable)]
  -- The three pieces are integrable.
  have hexp_int : Integrable (fun ω => Complex.exp (↑t * ↑(X ω) * Complex.I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with ω
      have heq : (↑t * ↑(X ω) * Complex.I : ℂ) = ↑(t * X ω) * Complex.I := by
        push_cast
        ring
      rw [heq]
      exact (Complex.norm_exp_ofReal_mul_I _).le)
  have hlin_int : Integrable (fun ω => ↑t * ↑(X ω) * Complex.I) μ := by
    have h := ((hX_int.ofReal).mul_const Complex.I).const_mul (↑t : ℂ)
    simpa [mul_assoc] using h
  have hconst_int : Integrable (fun _ : Ω => (1 : ℂ)) μ := integrable_const 1
  -- Rewrite the left side as the integral of the pointwise remainder.
  have hrem1_int : Integrable (fun ω => Complex.exp (↑t * ↑(X ω) * Complex.I) - 1) μ :=
    (hexp_int.sub hconst_int).congr (Filter.Eventually.of_forall fun ω => rfl)
  have hdecomp : (∫ ω, Complex.exp (↑t * ↑(X ω) * Complex.I) ∂μ - ∫ _, (1 : ℂ) ∂μ
        - ∫ ω, ↑t * ↑(X ω) * Complex.I ∂μ)
      = ∫ ω, (Complex.exp (↑t * ↑(X ω) * Complex.I) - 1 - ↑t * ↑(X ω) * Complex.I) ∂μ := by
    rw [← integral_sub hexp_int hconst_int, ← integral_sub hrem1_int hlin_int]
  have hone : ∫ _, (1 : ℂ) ∂μ = 1 := by simp
  have hlin : ∫ ω, ↑t * ↑(X ω) * Complex.I ∂μ = ↑t * Complex.I * ↑(∫ ω, X ω ∂μ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul (↑t * Complex.I)]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  have hrem_int : Integrable
      (fun ω => Complex.exp (↑t * ↑(X ω) * Complex.I) - 1 - ↑t * ↑(X ω) * Complex.I) μ :=
    ((hexp_int.sub hconst_int).sub hlin_int).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  rw [hchar, ← hone, ← hlin, hdecomp]
  calc ‖∫ ω, (Complex.exp (↑t * ↑(X ω) * Complex.I) - 1 - ↑t * ↑(X ω) * Complex.I) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (↑t * ↑(X ω) * Complex.I) - 1 - ↑t * ↑(X ω) * Complex.I‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, t ^ 2 * (X ω) ^ 2 ∂μ := by
        apply integral_mono_ae hrem_int.norm (hX_sq_int.const_mul (t ^ 2))
        filter_upwards with ω
        have h := norm_exp_ofReal_mul_I_sub_one_sub_le (t * X ω)
        have heq : (↑t * ↑(X ω) * Complex.I : ℂ) = ↑(t * X ω) * Complex.I := by
          push_cast
          ring
        calc ‖Complex.exp (↑t * ↑(X ω) * Complex.I) - 1 - ↑t * ↑(X ω) * Complex.I‖
            = ‖Complex.exp (↑(t * X ω) * Complex.I) - 1 - ↑(t * X ω) * Complex.I‖ := by
              rw [heq]
          _ ≤ (t * X ω) ^ 2 := h
          _ = t ^ 2 * (X ω) ^ 2 := by ring
    _ = t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
        rw [integral_const_mul]

/-- **First-order Taylor bound for the characteristic function.** Let $X$ be a measurable real
random variable on a probability space with $|X|$ integrable, and let $\varphi_X$ be the
characteristic function of the law of $X$. Then for every real $t$,
$|\varphi_X(t) - 1| \le |t| \, \mathbb{E}|X|$. -/
theorem norm_charFun_sub_one_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X) (hX_int : Integrable (fun ω => |X ω|) μ)
    (t : ℝ) :
    ‖charFun (μ.map X) t - 1‖ ≤ |t| * ∫ ω, |X ω| ∂μ := by
  have hX_ae : AEMeasurable X μ := hmeas.aemeasurable
  have hchar : charFun (μ.map X) t
      = ∫ ω, Complex.exp (↑t * ↑(X ω) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hX_ae
      ((by fun_prop : Measurable (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
        ).aestronglyMeasurable)]
  have hexp_int : Integrable (fun ω => Complex.exp (↑t * ↑(X ω) * Complex.I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (by
      filter_upwards with ω
      have heq : (↑t * ↑(X ω) * Complex.I : ℂ) = ↑(t * X ω) * Complex.I := by
        push_cast
        ring
      rw [heq]
      exact (Complex.norm_exp_ofReal_mul_I _).le)
  have hone : ∫ _, (1 : ℂ) ∂μ = 1 := by simp
  rw [hchar, ← hone, ← integral_sub hexp_int (integrable_const (1 : ℂ))]
  calc ‖∫ ω, (Complex.exp (↑t * ↑(X ω) * Complex.I) - 1) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (↑t * ↑(X ω) * Complex.I) - 1‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * |X ω| ∂μ := by
        have hrem1_int : Integrable
            (fun ω => Complex.exp (↑t * ↑(X ω) * Complex.I) - 1) μ :=
          (hexp_int.sub (integrable_const (1 : ℂ))).congr
            (Filter.Eventually.of_forall fun ω => rfl)
        apply integral_mono_ae hrem1_int.norm (hX_int.const_mul |t|)
        filter_upwards with ω
        have h : ‖Complex.exp (↑(t * X ω) * Complex.I) - 1‖ ≤ |t * X ω| := by
          simpa only [mul_comm, Real.norm_eq_abs] using
            (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * X ω))
        have heq : (↑t * ↑(X ω) * Complex.I : ℂ) = ↑(t * X ω) * Complex.I := by
          push_cast
          ring
        calc ‖Complex.exp (↑t * ↑(X ω) * Complex.I) - 1‖
            = ‖Complex.exp (↑(t * X ω) * Complex.I) - 1‖ := by rw [heq]
          _ ≤ |t * X ω| := h
          _ = |t| * |X ω| := abs_mul _ _
    _ = |t| * ∫ ω, |X ω| ∂μ := by rw [integral_const_mul]

/-- **Characteristic-function second-order bound.** Let $X$ be a measurable real random variable
on a probability space with $\mathbb{E}[X] = 0$ and $X^2$ integrable, and let $\varphi_X$ be the
characteristic function of the law of $X$. Then for every real $t$,
$|\varphi_X(t) - 1| \le t^2 \, \mathbb{E}[X^2]$. -/
theorem norm_charFun_sub_one_le_sq_mul_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hint2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (t : ℝ) :
    ‖charFun (μ.map X) t - 1‖ ≤ t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by
  have h := norm_charFun_sub_one_sub_le X hmeas hint2 t
  simp only [hmean, Complex.ofReal_zero, mul_zero, sub_zero] at h
  exact h

end MathlibExt.Probability.CharFunTaylorBounds
