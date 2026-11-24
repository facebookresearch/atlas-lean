/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianDensity
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Tactic.FunProp

/-!
# Common-covariance Gaussian likelihood ratio

For two multivariate Gaussians with a common positive-definite
covariance `R` and different means, the laws are mutually
absolutely continuous, and the Radon--Nikodym derivative of
`N(s1, R)` with respect to `N(s0, R)` is the exponential of the
log-likelihood ratio `(s1 - s0)ᵀ R⁻¹ y - (s1ᵀ R⁻¹ s1 - s0ᵀ R⁻¹ s0)/2`,
both Lebesgue-almost everywhere and `N(s0, R)`-almost everywhere.
Equal means give log-ratio `0` and derivative `1`. The shared
density input is the canonical
`MetaMathlibExt.multivariateGaussian_eq_withDensity`; private
`_of_density` variants take it as a hypothesis and the public
theorems discharge it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Distributions.CommonCovarianceLikelihood

-- Private helpers for the proofs below (not part of the pin).

private theorem pdf_measurable {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) :
    Measurable (fun x => MetaMathlibExt.multivariateGaussianPDFReal s R x) := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  fun_prop

private theorem pdf_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (y : EuclideanSpace ℝ ι) :
    0 < MetaMathlibExt.multivariateGaussianPDFReal s R y := by
  unfold MetaMathlibExt.multivariateGaussianPDFReal
  have h1 : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < √R.det := Real.sqrt_pos.2 hR.det_pos
  positivity

/-- The common-covariance Gaussian log-likelihood ratio statistic
`(s1 - s0)ᵀ R⁻¹ y - (s1ᵀ R⁻¹ s1 - s0ᵀ R⁻¹ s0) / 2`. -/
noncomputable def commonCovarianceLogLR {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  ofLp (s1 - s0) ⬝ᵥ R⁻¹ *ᵥ ofLp y -
    (ofLp s1 ⬝ᵥ R⁻¹ *ᵥ ofLp s1 - ofLp s0 ⬝ᵥ R⁻¹ *ᵥ ofLp s0) / 2

/-- Pointwise density ratio: for positive definite `R`, the quotient of the two Gaussian
densities with common covariance is `exp` of the affine statistic. -/
theorem multivariateGaussianPDFReal_div_eq_exp {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (y : EuclideanSpace ℝ ι) :
    MetaMathlibExt.multivariateGaussianPDFReal s1 R y /
        MetaMathlibExt.multivariateGaussianPDFReal s0 R y =
      Real.exp (commonCovarianceLogLR s1 s0 R y) := by
  have hT : (R⁻¹)ᵀ = R⁻¹ := hR.inv.isHermitian.isSymm
  have hsym : ∀ u v : ι → ℝ, u ⬝ᵥ R⁻¹ *ᵥ v = v ⬝ᵥ R⁻¹ *ᵥ u := fun u v => by
    conv_lhs => rw [← hT]
    exact Matrix.dotProduct_transpose_mulVec _ _ _
  have hdet : 0 < R.det := hR.det_pos
  have hC : ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√R.det)⁻¹ ≠ 0 := by positivity
  unfold MetaMathlibExt.multivariateGaussianPDFReal commonCovarianceLogLR
  rw [mul_div_mul_left _ _ hC, ← Real.exp_sub]
  congr 1
  simp only [WithLp.ofLp_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_sub]
  linear_combination (1 / 2 : ℝ) * hsym (ofLp y) (ofLp s1) -
    (1 / 2 : ℝ) * hsym (ofLp y) (ofLp s0)

/-- Generic Radon-Nikodym quotient: over a σ-finite base `ν`, for measurable strictly
positive real densities `f` and `g`, `d(ν.withDensity f)/d(ν.withDensity g) = f / g`
`ν`-almost everywhere. -/
theorem rnDeriv_withDensity_ofReal_eq_div {α : Type} [MeasurableSpace α] (ν : Measure α)
    [SigmaFinite ν] (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x) :
    (ν.withDensity fun x => ENNReal.ofReal (f x)).rnDeriv
        (ν.withDensity fun x => ENNReal.ofReal (g x)) =ᵐ[ν]
      fun x => ENNReal.ofReal (f x / g x) := by
  have hF : Measurable (fun x => ENNReal.ofReal (f x)) := hf.ennreal_ofReal
  have hG : Measurable (fun x => ENNReal.ofReal (g x)) := hg.ennreal_ofReal
  have h1 : (ν.withDensity fun x => ENNReal.ofReal (f x)).rnDeriv
        (ν.withDensity fun x => ENNReal.ofReal (g x)) =ᵐ[ν]
        fun x => (ENNReal.ofReal (g x))⁻¹ *
          (ν.withDensity fun x => ENNReal.ofReal (f x)).rnDeriv ν x := by
    refine MeasureTheory.Measure.rnDeriv_withDensity_right _ _ hG.aemeasurable ?_ ?_
    · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (hgpos x)
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  have h2 : (ν.withDensity fun x => ENNReal.ofReal (f x)).rnDeriv ν =ᵐ[ν]
      fun x => ENNReal.ofReal (f x) := by
    apply MeasureTheory.Measure.rnDeriv_withDensity
    exact hF
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  rw [hx, ENNReal.ofReal_div_of_pos (hgpos x), div_eq_mul_inv]
  exact mul_comm _ _

/-- Common-covariance Gaussians are mutually absolutely continuous; one direction:
`N(s1, R) ≪ N(s0, R)`, given the shared density theorem at both means. -/
private theorem multivariateGaussian_absolutelyContinuous_common_covariance_of_density {ι : Type} [Fintype ι]
    [DecidableEq ι] (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (hd1 : multivariateGaussian s1 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s1 R x))
    (hd0 : multivariateGaussian s0 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s0 R x)) :
    multivariateGaussian s1 R ≪ multivariateGaussian s0 R := by
  rw [hd1, hd0]
  have h1 : volume.withDensity (fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s1 R x)) ≪ volume := by
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h2 : volume ≪ volume.withDensity (fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s0 R x)) := by
    refine MeasureTheory.withDensity_absolutelyContinuous' (pdf_measurable s0 R).ennreal_ofReal.aemeasurable ?_
    exact Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_ne_zero_iff.mpr (pdf_pos s0 R hR x)
  exact h1.trans h2

/-- **Common-covariance Gaussian likelihood ratio.** For positive definite `R`, given the
shared density theorem at `s1` and `s0`, the Radon-Nikodym derivative of `N(s1, R)` with
respect to `N(s0, R)` is `exp ((s1 - s0)ᵀ R⁻¹ y - (s1ᵀ R⁻¹ s1 - s0ᵀ R⁻¹ s0) / 2)`
for Lebesgue-almost every `y`. -/
private theorem rnDeriv_multivariateGaussian_common_covariance_of_density {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (hd1 : multivariateGaussian s1 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s1 R x))
    (hd0 : multivariateGaussian s0 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s0 R x)) :
    (multivariateGaussian s1 R).rnDeriv (multivariateGaussian s0 R) =ᵐ[volume]
      fun y => ENNReal.ofReal (Real.exp (commonCovarianceLogLR s1 s0 R y)) := by
  rw [hd1, hd0]
  have h := rnDeriv_withDensity_ofReal_eq_div volume _ _
    (pdf_measurable s1 R) (pdf_measurable s0 R)
    (fun x => pdf_pos s1 R hR x) (fun x => pdf_pos s0 R hR x)
  refine h.trans ?_
  filter_upwards with y
  congr 1
  exact multivariateGaussianPDFReal_div_eq_exp s1 s0 R hR y

/-- The same likelihood ratio, almost everywhere under the reference law `N(s0, R)`. -/
private theorem rnDeriv_multivariateGaussian_common_covariance_ae_reference_of_density {ι : Type} [Fintype ι]
    [DecidableEq ι] (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (hd1 : multivariateGaussian s1 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s1 R x))
    (hd0 : multivariateGaussian s0 R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s0 R x)) :
    (multivariateGaussian s1 R).rnDeriv (multivariateGaussian s0 R) =ᵐ[multivariateGaussian s0 R]
      fun y => ENNReal.ofReal (Real.exp (commonCovarianceLogLR s1 s0 R y)) := by
  have hac : multivariateGaussian s0 R ≪ volume := by
    rw [hd0]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact hac.ae_eq (rnDeriv_multivariateGaussian_common_covariance_of_density s1 s0 R hR hd1 hd0)

/-- Validation: equal means give log-likelihood ratio `0`. -/
theorem commonCovarianceLogLR_self {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (y : EuclideanSpace ℝ ι) :
    commonCovarianceLogLR s s R y = 0 := by
  unfold commonCovarianceLogLR
  rw [WithLp.ofLp_sub]
  simp only [sub_self, zero_dotProduct, zero_div]

/-- Validation: equal means give Radon-Nikodym ratio `1`, Lebesgue-almost everywhere. -/
private theorem rnDeriv_multivariateGaussian_self_eq_one_of_density {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef)
    (hd : multivariateGaussian s R =
      volume.withDensity fun x => ENNReal.ofReal (MetaMathlibExt.multivariateGaussianPDFReal s R x)) :
    (multivariateGaussian s R).rnDeriv (multivariateGaussian s R) =ᵐ[volume] fun _ => 1 := by
  have hvolμ : volume ≪ multivariateGaussian s R := by
    rw [hd]
    refine MeasureTheory.withDensity_absolutelyContinuous' (pdf_measurable s R).ennreal_ofReal.aemeasurable ?_
    exact Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_ne_zero_iff.mpr (pdf_pos s R hR x)
  have hself : (multivariateGaussian s R).rnDeriv (multivariateGaussian s R) =ᵐ[multivariateGaussian s R] fun _ => 1 :=
    MeasureTheory.Measure.rnDeriv_self _
  exact hvolμ.ae_eq hself

/-- Validation, `n = 1`: with `R = [v]` the statistic is the scalar Gaussian
log-likelihood ratio `(m1 - m0) y / v - (m1² - m0²) / (2 v)`. -/
theorem commonCovarianceLogLR_fin_one (m1 m0 v y : ℝ) :
    commonCovarianceLogLR (toLp 2 ![m1]) (toLp 2 ![m0]) (!![v] : Matrix (Fin 1) (Fin 1) ℝ)
        (toLp 2 ![y]) =
      (m1 - m0) * y / v - (m1 ^ 2 - m0 ^ 2) / (2 * v) := by
  have hinv : (!![v] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![v⁻¹] := by
    rw [Matrix.inv_def, Matrix.det_fin_one_of, Matrix.adjugate_fin_one, Ring.inverse_eq_inv]
    ext i j
    fin_cases i; fin_cases j; simp
  unfold commonCovarianceLogLR
  rw [hinv]
  simp only [WithLp.ofLp_sub, dotProduct, Matrix.mulVec,
    Fin.sum_univ_one]
  simp [div_eq_mul_inv]
  ring

/-- Validation, `n = 1`: Mathlib's scalar Gaussian densities with a common nonzero
variance `v` have ratio `exp ((m1 - m0) y / v - (m1² - m0²) / (2 v))`. -/
theorem gaussianPDFReal_div_eq_exp (m1 m0 : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (y : ℝ) :
    gaussianPDFReal m1 v y / gaussianPDFReal m0 v y =
      Real.exp ((m1 - m0) * y / v - (m1 ^ 2 - m0 ^ 2) / (2 * v)) := by
  have hvRpos : (0 : ℝ) < (v : ℝ) := by positivity
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal
  rw [mul_div_mul_left _ _ ?_, ← Real.exp_sub]
  · congr 1
    field_simp
    ring
  · positivity

/-- Violated premise: with unequal variances (`2` against `1`, common mean `0`) the scalar
density ratio is not `exp` of any affine function of `y`; a quadratic statistic is needed. -/
theorem not_exists_affine_log_gaussianPDFReal_ratio_of_ne_variance :
    ¬ ∃ a b : ℝ, ∀ y : ℝ,
      gaussianPDFReal 0 2 y / gaussianPDFReal 0 1 y = Real.exp (a * y + b) := by
  rintro ⟨a, b, h⟩
  have h1 := h 1
  have hm1 := h (-1)
  have h0 := h 0
  have heven : gaussianPDFReal 0 2 1 / gaussianPDFReal 0 1 1 =
      gaussianPDFReal 0 2 (-1) / gaussianPDFReal 0 1 (-1) := by
    unfold gaussianPDFReal
    norm_num
  rw [h1, hm1] at heven
  have ha : a = 0 := by
    have hinj := Real.exp_injective heven
    linarith
  rw [ha] at h0 h1
  simp only [zero_mul, zero_add] at h0 h1
  have h01 : gaussianPDFReal 0 2 0 / gaussianPDFReal 0 1 0 =
      gaussianPDFReal 0 2 1 / gaussianPDFReal 0 1 1 :=
    h0.trans h1.symm
  unfold gaussianPDFReal at h01
  simp only [sub_self, sub_zero, zero_pow two_ne_zero, one_pow, neg_zero, zero_div,
    Real.exp_zero, mul_one] at h01
  have hC2 : (√(2 * Real.pi * ((2 : ℝ≥0) : ℝ)))⁻¹ ≠ 0 := by positivity
  have hC1 : (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ ≠ 0 := by positivity
  rw [mul_div_mul_comm] at h01
  have hX : (√(2 * Real.pi * ((2 : ℝ≥0) : ℝ)))⁻¹ / (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ ≠ 0 :=
    div_ne_zero hC2 hC1
  have hE : Real.exp (-1 / (2 * ((2 : ℝ≥0) : ℝ))) / Real.exp (-1 / (2 * ((1 : ℝ≥0) : ℝ))) = 1 := by
    have h2 : (√(2 * Real.pi * ((2 : ℝ≥0) : ℝ)))⁻¹ / (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ * 1 =
        (√(2 * Real.pi * ((2 : ℝ≥0) : ℝ)))⁻¹ / (√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
          (Real.exp (-1 / (2 * ((2 : ℝ≥0) : ℝ))) / Real.exp (-1 / (2 * ((1 : ℝ≥0) : ℝ)))) := by
      rw [mul_one]
      exact h01
    have h3 := mul_left_cancel₀ hX h2
    exact h3.symm
  rw [← Real.exp_sub] at hE
  rw [← Real.exp_zero] at hE
  have hD := Real.exp_injective hE
  norm_num at hD



/-- **Absolute continuity, density discharged.** The shared density
is `MetaMathlibExt.multivariateGaussian_eq_withDensity`. -/
theorem multivariateGaussian_absolutelyContinuous_common_covariance {ι : Type} [Fintype ι]
    [DecidableEq ι] (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) :
    multivariateGaussian s1 R ≪ multivariateGaussian s0 R :=
  multivariateGaussian_absolutelyContinuous_common_covariance_of_density s1 s0 R hR
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s1 hR)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s0 hR)

/-- **Common-covariance Gaussian likelihood ratio, density
discharged.** The Radon--Nikodym derivative of `N(s1, R)` with
respect to `N(s0, R)` is the exponential of the common-covariance
log-likelihood ratio, Lebesgue-almost everywhere. -/
theorem rnDeriv_multivariateGaussian_common_covariance {ι : Type} [Fintype ι] [DecidableEq ι]
    (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) :
    (multivariateGaussian s1 R).rnDeriv (multivariateGaussian s0 R) =ᵐ[volume]
      fun y => ENNReal.ofReal (Real.exp (commonCovarianceLogLR s1 s0 R y)) :=
  rnDeriv_multivariateGaussian_common_covariance_of_density s1 s0 R hR
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s1 hR)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s0 hR)

/-- The same likelihood ratio, almost everywhere under the
reference law `N(s0, R)`, density discharged. -/
theorem rnDeriv_multivariateGaussian_common_covariance_ae_reference {ι : Type} [Fintype ι]
    [DecidableEq ι] (s1 s0 : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) :
    (multivariateGaussian s1 R).rnDeriv (multivariateGaussian s0 R)
      =ᵐ[multivariateGaussian s0 R]
      fun y => ENNReal.ofReal (Real.exp (commonCovarianceLogLR s1 s0 R y)) :=
  rnDeriv_multivariateGaussian_common_covariance_ae_reference_of_density s1 s0 R hR
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s1 hR)
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s0 hR)

/-- Equal means give Radon--Nikodym ratio `1`, Lebesgue-almost
everywhere, density discharged. -/
theorem rnDeriv_multivariateGaussian_self_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : EuclideanSpace ℝ ι) (R : Matrix ι ι ℝ) (hR : R.PosDef) :
    (multivariateGaussian s R).rnDeriv (multivariateGaussian s R) =ᵐ[volume] fun _ => 1 :=
  rnDeriv_multivariateGaussian_self_eq_one_of_density s R hR
    (MetaMathlibExt.multivariateGaussian_eq_withDensity s hR)

end MathlibExt.Probability.Distributions.CommonCovarianceLikelihood
