/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The density of the multivariate Gaussian

Mathlib defines `multivariateGaussian μ S` as the image of the standard Gaussian on
`EuclideanSpace ℝ ι` under `x ↦ μ + √S x`, without a density. For positive definite `S` this file
proves the textbook density formula.

Main results:

* `stdGaussian_eq_withDensity`: the standard Gaussian has density
  `stdGaussianPDFReal v = (2π)^(-n/2) exp (-‖v‖² / 2)`, proved by comparing characteristic functions
  (Mathlib's Gaussian integral `integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace`).
* `map_withDensity_measurableEquiv`, `affineEquiv`, `map_affineEquiv_volume`: change of variables
  under `x ↦ μ + A x` for an invertible matrix `A` (Lebesgue measure scales by `|det A|⁻¹`).
* `norm_sq_sqrt_inv_apply`: `‖√S⁻¹ u‖² = uᵀ S⁻¹ u`.
* `multivariateGaussian_eq_withDensity`: **for positive definite `S`, `multivariateGaussian μ S`
  has density `(2π)^(-n/2) det(S)^(-1/2) exp (-(x - μ)ᵀ S⁻¹ (x - μ) / 2)`**
  (`multivariateGaussianPDFReal`).

`GaussianDirectionUniformity.lean` in
`FormalizedTextbooks/HighDimensionalProbability/Chapter03/Section02/Examples/` proves the
standard-Gaussian density privately for `Fin n`, by products of one-dimensional densities; this
file uses characteristic functions instead and covers the general case.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open MeasureTheory ProbabilityTheory Complex Matrix WithLp
open scoped RealInnerProductSpace MatrixOrder

variable {ι : Type*} [Fintype ι]

/-- The standard Gaussian density on `EuclideanSpace ℝ ι`:
`(2π)^(-n/2) exp (-‖v‖² / 2)`. -/
noncomputable def stdGaussianPDFReal (v : EuclideanSpace ℝ ι) : ℝ :=
  ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * Real.exp (-(‖v‖ ^ 2) / 2)

theorem stdGaussianPDFReal_nonneg (v : EuclideanSpace ℝ ι) : 0 ≤ stdGaussianPDFReal v := by
  unfold stdGaussianPDFReal; positivity

theorem measurable_stdGaussianPDFReal : Measurable (stdGaussianPDFReal (ι := ι)) := by
  unfold stdGaussianPDFReal; fun_prop

theorem integrable_stdGaussianPDFReal : Integrable (stdGaussianPDFReal (ι := ι)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < ((1 / 2 : ℝ) : ℂ).re by norm_num) 0 (0 : EuclideanSpace ℝ ι)).norm
  refine (h.const_mul ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹).congr (ae_of_all _ fun v => ?_)
  simp only [stdGaussianPDFReal, zero_mul, add_zero, norm_exp]
  congr 1
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  norm_cast
  ring_nf

/-- The standard Gaussian density as a measure. -/
noncomputable def stdGaussianDensityMeasure : Measure (EuclideanSpace ℝ ι) :=
  volume.withDensity fun v => ENNReal.ofReal (stdGaussianPDFReal v)

instance : IsFiniteMeasure (stdGaussianDensityMeasure (ι := ι)) :=
  isFiniteMeasure_withDensity_ofReal integrable_stdGaussianPDFReal.hasFiniteIntegral

theorem two_pi_cpow_card :
    ((√(2 * Real.pi)) ^ Fintype.card ι : ℂ) = ((Real.pi : ℂ) / (1 / 2 : ℂ)) ^
      ((Fintype.card ι : ℂ) / 2) := by
  have h2 : (Real.pi : ℂ) / (1 / 2 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [h2, show ((Fintype.card ι : ℂ) / 2) = ((Fintype.card ι / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← ofReal_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  ring_nf

theorem charFun_stdGaussianDensityMeasure (t : EuclideanSpace ℝ ι) :
    charFun (stdGaussianDensityMeasure (ι := ι)) t = cexp (-(‖t‖ ^ 2) / 2) := by
  rw [charFun_apply, stdGaussianDensityMeasure]
  change ∫ v, cexp (⟪v, t⟫ * I) ∂(volume.withDensity fun v =>
    ((stdGaussianPDFReal v).toNNReal : ENNReal)) = _
  rw [integral_withDensity_eq_integral_smul (measurable_stdGaussianPDFReal.real_toNNReal)]
  have hint : ∀ v : EuclideanSpace ℝ ι, (stdGaussianPDFReal v).toNNReal • cexp (⟪v, t⟫ * I) =
      (((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ : ℂ) *
        cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + I * ⟪t, v⟫) := by
    intro v
    rw [NNReal.smul_def, Real.coe_toNNReal _ (stdGaussianPDFReal_nonneg v), stdGaussianPDFReal,
      real_inner_comm, Complex.real_smul]
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hint]
  rw [integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace (by norm_num) I t,
    ← two_pi_cpow_card, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ (ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')),
    one_mul]
  congr 1
  rw [I_sq]
  ring

/-- **The standard Gaussian has density** `(2π)^(-n/2) exp (-‖v‖² / 2)`. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity fun v => ENNReal.ofReal (stdGaussianPDFReal v) := by
  change _ = stdGaussianDensityMeasure
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_stdGaussianDensityMeasure]

/-- Pushing a measure with density through a measurable equivalence. -/
theorem map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (ν : Measure α) {g : α → ENNReal} :
    (ν.withDensity g).map e = (ν.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, lintegral_map_equiv]
  simp

variable [DecidableEq ι]

/-- The affine map `x ↦ μ + A x` of an invertible matrix, as a measurable equivalence. -/
noncomputable def affineEquiv (μ : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι where
  toFun x := μ + toEuclideanCLM (𝕜 := ℝ) A x
  invFun y := toEuclideanCLM (𝕜 := ℝ) A⁻¹ (y - μ)
  left_inv x := by
    simp only [add_sub_cancel_left]
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      nonsing_inv_mul _ hA, map_one]
    rfl
  right_inv y := by
    simp only
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      mul_nonsing_inv _ hA, map_one]
    exact add_sub_cancel μ y
  measurable_toFun := by
    change Measurable fun x => μ + toEuclideanCLM (𝕜 := ℝ) A x
    fun_prop
  measurable_invFun := by
    change Measurable fun y => toEuclideanCLM (𝕜 := ℝ) A⁻¹ (y - μ)
    fun_prop

theorem det_toEuclideanCLM (A : Matrix ι ι ℝ) :
    LinearMap.det (toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) =
      A.det := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- Lebesgue measure under `x ↦ μ + A x` scales by `|det A|⁻¹`. -/
theorem map_affineEquiv_volume (μ : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    (volume : Measure (EuclideanSpace ℝ ι)).map (affineEquiv μ A hA) =
      ENNReal.ofReal |(A.det)⁻¹| • volume := by
  have hdet : LinearMap.det (toEuclideanCLM (𝕜 := ℝ) A :
      EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ 0 := by
    rw [det_toEuclideanCLM]; exact hA.ne_zero
  have hT : ⇑(affineEquiv μ A hA) = (fun y => μ + y) ∘ (toEuclideanCLM (𝕜 := ℝ) A) := rfl
  rw [hT, ← Measure.map_map (measurable_const_add μ)
    (toEuclideanCLM (𝕜 := ℝ) A).continuous.measurable]
  have hL := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (EuclideanSpace ℝ ι)) hdet
  rw [det_toEuclideanCLM] at hL
  change Measure.map (⇑(toEuclideanCLM (𝕜 := ℝ) A :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)) volume = _ at hL
  rw [show ⇑(toEuclideanCLM (𝕜 := ℝ) A) = ⇑(toEuclideanCLM (𝕜 := ℝ) A :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) from rfl, hL, Measure.map_smul,
    map_add_left_eq_self]
  exact (measurable_const_add μ).aemeasurable

/-- The multivariate Gaussian density
`(2π)^(-n/2) det(S)^(-1/2) exp (-(x - μ)ᵀ S⁻¹ (x - μ) / 2)`. -/
noncomputable def multivariateGaussianPDFReal (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ((√(2 * Real.pi)) ^ Fintype.card ι)⁻¹ * (√S.det)⁻¹ *
    Real.exp (-(ofLp (x - μ) ⬝ᵥ S⁻¹ *ᵥ ofLp (x - μ)) / 2)

/-- `‖√S⁻¹ u‖² = uᵀ S⁻¹ u` for positive definite `S`. -/
theorem norm_sq_sqrt_inv_apply {S : Matrix ι ι ℝ} (hS : S.PosDef) (u : EuclideanSpace ℝ ι) :
    ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ u‖ ^ 2 = ofLp u ⬝ᵥ S⁻¹ *ᵥ ofLp u := by
  have hinv : (CFC.sqrt S)⁻¹ = CFC.sqrt S⁻¹ := hS.posSemidef.inv_sqrt
  have hsa : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) := by
    rw [hinv]; exact (CFC.sqrt_nonneg S⁻¹).isSelfAdjoint.map _
  have hsq : (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by
    rw [hinv, CFC.sqrt_mul_sqrt_self _ hS.posSemidef.inv.nonneg]
  rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hsq,
    inner_toEuclideanCLM]

/-- **The multivariate Gaussian density**: for positive definite `S`, `multivariateGaussian μ S`
has density `(2π)^(-n/2) det(S)^(-1/2) exp (-(x - μ)ᵀ S⁻¹ (x - μ) / 2)` with respect to
Lebesgue measure. -/
theorem multivariateGaussian_eq_withDensity (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosDef) :
    multivariateGaussian μ S =
      volume.withDensity fun x => ENNReal.ofReal (multivariateGaussianPDFReal μ S x) := by
  have hdetA : (CFC.sqrt S).det = √S.det := by
    rw [hS.posSemidef.det_sqrt, RCLike.sqrt_real]
  have hdetpos : 0 < (CFC.sqrt S).det := by rw [hdetA]; exact Real.sqrt_pos.2 hS.det_pos
  have hU : IsUnit (CFC.sqrt S).det := hdetpos.ne'.isUnit
  have hmap : multivariateGaussian μ S =
      (stdGaussian (EuclideanSpace ℝ ι)).map (affineEquiv μ (CFC.sqrt S) hU) := rfl
  rw [hmap, stdGaussian_eq_withDensity, map_withDensity_measurableEquiv, map_affineEquiv_volume,
    withDensity_smul_measure, ← withDensity_smul _
      (f := (fun v => ENNReal.ofReal (stdGaussianPDFReal v)) ∘ (affineEquiv μ (CFC.sqrt S) hU).symm)
      ((ENNReal.measurable_ofReal.comp measurable_stdGaussianPDFReal).comp
        (affineEquiv μ (CFC.sqrt S) hU).symm.measurable)]
  congr 1
  funext x
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  change |(CFC.sqrt S).det⁻¹| * stdGaussianPDFReal
    (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ (x - μ)) = _
  rw [stdGaussianPDFReal, norm_sq_sqrt_inv_apply hS, multivariateGaussianPDFReal, hdetA,
    abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hS.det_pos))]
  ring

end MetaMathlibExt
