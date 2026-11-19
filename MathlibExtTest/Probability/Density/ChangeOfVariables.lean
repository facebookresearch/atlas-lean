/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Density.ChangeOfVariables
import MathlibExt.Probability.Distributions.GaussianDensity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for densities under a change of variables

Positive, boundary, negative and nonvacuity checks for
`MathlibExt.Probability.Density.ChangeOfVariables`: the affine flow `z ↦ 2 z + 1` on `ℝ` with a
generic and a standard Gaussian base, a two-layer flow, the Jacobian-matrix form on `ℝ²`, and the
affine Gaussian flow `z ↦ b + A z`.
-/

open MetaMathlibExt MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal MatrixOrder

namespace ChangeOfVariablesTest

/-! ## A one-dimensional affine flow `z ↦ 2 z + 1` -/

/-- The affine flow `z ↦ 2 z + 1` on `ℝ`. -/
noncomputable def affineFlow : ℝ ≃ᵐ ℝ where
  toFun z := 2 * z + 1
  invFun x := (x - 1) / 2
  left_inv z := by simp only; ring
  right_inv x := by simp only; ring
  measurable_toFun := by change Measurable fun z : ℝ => 2 * z + 1; fun_prop
  measurable_invFun := by change Measurable fun x : ℝ => (x - 1) / 2; fun_prop

theorem hasFDerivAt_affineFlow (z : ℝ) :
    HasFDerivAt affineFlow (ContinuousLinearMap.toSpanSingleton ℝ (2 : ℝ)) z := by
  have h := ((hasDerivAt_id z).const_mul (2 : ℝ)).add_const (1 : ℝ)
  rw [mul_one] at h
  exact h.hasFDerivAt

theorem hasFDerivAt_affineFlow_symm (x : ℝ) :
    HasFDerivAt affineFlow.symm (ContinuousLinearMap.toSpanSingleton ℝ (2⁻¹ : ℝ)) x := by
  have h := ((hasDerivAt_id x).sub_const (1 : ℝ)).div_const (2 : ℝ)
  rw [one_div] at h
  exact h.hasFDerivAt

-- The density of `2 Z + 1` is `x ↦ p ((x - 1) / 2) / 2`.
example (p : ℝ → ℝ≥0∞) :
    (volume.withDensity p).map affineFlow =
      volume.withDensity fun x => p ((x - 1) / 2) * ENNReal.ofReal 2⁻¹ := by
  rw [map_withDensity_eq_withDensity_abs_det_fderiv_symm volume affineFlow
    hasFDerivAt_affineFlow_symm p]
  simp only [ContinuousLinearMap.det_toSpanSingleton, abs_inv, abs_two]
  rfl

-- Forward log form for `2 Z + 1`: `log p_X (2 z + 1) = log p_Z z - log 2`.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) [HasPDF Z P volume] :
    ∀ᵐ z ∂volume, pdf Z P volume z ≠ 0 → pdf Z P volume z ≠ ∞ →
      Real.log (pdf (affineFlow ∘ Z) P volume (2 * z + 1)).toReal =
        Real.log (pdf Z P volume z).toReal - Real.log 2 := by
  filter_upwards [log_pdf_comp_apply_ae volume affineFlow hasFDerivAt_affineFlow
    hasFDerivAt_affineFlow_symm Z P] with z hz h0 htop
  have h := hz h0 htop
  rw [show affineFlow z = 2 * z + 1 from rfl] at h
  simpa [ContinuousLinearMap.det_toSpanSingleton] using h

/-! ## A concrete base density: the standard Gaussian -/

theorem hasPDF_id_gaussianReal : HasPDF (id : ℝ → ℝ) (gaussianReal 0 1) volume :=
  hasPDF_of_map_eq_withDensity aemeasurable_id _ (measurable_gaussianPDF 0 1).aemeasurable
    (by rw [Measure.map_id, gaussianReal_of_var_ne_zero 0 one_ne_zero])

theorem pdf_id_gaussianReal :
    pdf (id : ℝ → ℝ) (gaussianReal 0 1) volume =ᵐ[volume] gaussianPDF 0 1 := by
  have := hasPDF_id_gaussianReal
  exact (pdf.eq_of_map_eq_withDensity' (X := (id : ℝ → ℝ)) _
    (measurable_gaussianPDF 0 1).aemeasurable).1
    (by rw [Measure.map_id, gaussianReal_of_var_ne_zero 0 one_ne_zero])

-- For a standard Gaussian base `Z` and `X = 2 Z + 1`, the log-likelihood identity holds with no
-- side condition: `log p_X (2 z + 1) = log φ(z) - log 2` for almost every `z`.
example : ∀ᵐ z ∂volume,
    Real.log (pdf (affineFlow ∘ id) (gaussianReal 0 1) volume (2 * z + 1)).toReal =
      Real.log (gaussianPDFReal 0 1 z) - Real.log 2 := by
  have := hasPDF_id_gaussianReal
  filter_upwards [log_pdf_comp_apply_ae volume affineFlow hasFDerivAt_affineFlow
    hasFDerivAt_affineFlow_symm id (gaussianReal 0 1), pdf_id_gaussianReal] with z hz hg
  have hpos := gaussianPDFReal_pos 0 1 z one_ne_zero
  have h0 : pdf id (gaussianReal 0 1) volume z ≠ 0 := by
    rw [hg, gaussianPDF_def]; exact ENNReal.ofReal_pos.2 hpos |>.ne'
  have htop : pdf id (gaussianReal 0 1) volume z ≠ ∞ := by
    rw [hg, gaussianPDF_def]; exact ENNReal.ofReal_ne_top
  have h := hz h0 htop
  rw [hg, gaussianPDF_def, ENNReal.toReal_ofReal hpos.le,
    show affineFlow z = 2 * z + 1 from rfl] at h
  simpa [ContinuousLinearMap.det_toSpanSingleton] using h

-- Boundary check: without positivity of the base density the real-log identity is false, since
-- `Real.log 0 = 0` while `log |det DT| = log 2 ≠ 0`.
example : Real.log ((0 : ℝ≥0∞) * ENNReal.ofReal |(2 : ℝ)|⁻¹).toReal ≠
    Real.log (0 : ℝ≥0∞).toReal - Real.log |(2 : ℝ)| := by
  simp only [zero_mul, ENNReal.toReal_zero, Real.log_zero, zero_sub, abs_two]
  exact (neg_ne_zero.2 (Real.log_pos one_lt_two).ne').symm

-- Negative check: a non-injective map such as squaring is not a measurable equivalence, so it is
-- excluded from the hypotheses.
example : ¬ ∃ T : ℝ ≃ᵐ ℝ, ⇑T = fun z => z ^ 2 := by
  rintro ⟨T, hT⟩
  have h : T (-1) = T 1 := by rw [hT]; norm_num
  exact absurd (T.injective h) (by norm_num)

/-! ## Two layers: composition adds log-determinants -/

-- Stacking `z ↦ 2 z + 1` twice: `log p_X x = log p_Z (T⁻¹ (T⁻¹ x)) - log 2 - log 2`.
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) [HasPDF Z P volume] :
    ∀ᵐ x ∂volume, pdf Z P volume (affineFlow.symm (affineFlow.symm x)) ≠ 0 →
      pdf Z P volume (affineFlow.symm (affineFlow.symm x)) ≠ ∞ →
      Real.log (pdf (affineFlow ∘ affineFlow ∘ Z) P volume x).toReal =
        Real.log (pdf Z P volume (affineFlow.symm (affineFlow.symm x))).toReal -
          Real.log 2 - Real.log 2 := by
  filter_upwards [log_pdf_trans_ae volume affineFlow affineFlow hasFDerivAt_affineFlow_symm
    hasFDerivAt_affineFlow_symm Z P] with x hx h0 htop
  have h := hx h0 htop (by simp) (by simp)
  simp only [ContinuousLinearMap.det_toSpanSingleton, abs_inv, abs_two, Real.log_inv] at h
  rw [h]
  ring

/-! ## Coordinates: the Jacobian-matrix form on `Fin 2 → ℝ` -/

-- The flow `x ↦ 2 • x` on `ℝ²` has inverse Jacobian determinant `1 / 4`.
example (p : (Fin 2 → ℝ) → ℝ≥0∞) :
    (volume.withDensity p).map
        (MeasurableEquiv.smul₀ (α := Fin 2 → ℝ) (2 : ℝ) two_ne_zero) =
      volume.withDensity fun x => p ((2⁻¹ : ℝ) • x) * ENNReal.ofReal (1 / 4) := by
  have hsymm : ⇑(MeasurableEquiv.smul₀ (α := Fin 2 → ℝ) (2 : ℝ) two_ne_zero).symm =
      fun y : Fin 2 → ℝ => ((2⁻¹ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ y := by
    rw [MeasurableEquiv.symm_smul₀]
    funext y
    rw [smul_mulVec, one_mulVec]
    rfl
  have hdiff :
      Differentiable ℝ (MeasurableEquiv.smul₀ (α := Fin 2 → ℝ) (2 : ℝ) two_ne_zero).symm := by
    rw [MeasurableEquiv.symm_smul₀]
    exact differentiable_id.const_smul (2⁻¹ : ℝ)
  rw [map_withDensity_eq_withDensity_abs_det_jacobianMatrix_symm _ hdiff p]
  congr 1
  funext x
  rw [hsymm, jacobianMatrix_fun_mulVec, det_smul, det_one, ← hsymm, MeasurableEquiv.symm_smul₀]
  norm_num

/-! ## The affine Gaussian flow `z ↦ b + A z` (positive check) -/

theorem hasFDerivAt_affineEquiv_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (hA : IsUnit A.det) (x : EuclideanSpace ℝ ι) :
    HasFDerivAt (affineEquiv b A hA).symm (toEuclideanCLM (𝕜 := ℝ) A⁻¹) x := by
  have h := (toEuclideanCLM (𝕜 := ℝ) A⁻¹).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const b)
  rw [ContinuousLinearMap.comp_id] at h
  exact h

-- The flow `z ↦ b + A z` pushes the standard Gaussian to the density
-- `x ↦ φ (A⁻¹ (x - b)) * |det A⁻¹|`, by the change-of-variables theorem.
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (affineEquiv b A hA) =
      volume.withDensity fun x =>
        ENNReal.ofReal (stdGaussianPDFReal (toEuclideanCLM (𝕜 := ℝ) A⁻¹ (x - b))) *
          ENNReal.ofReal |A⁻¹.det| := by
  rw [stdGaussian_eq_withDensity, map_withDensity_eq_withDensity_abs_det_fderiv_symm volume
    (affineEquiv b A hA) (hasFDerivAt_affineEquiv_symm b A hA)]
  congr 1
  funext x
  rw [show (toEuclideanCLM (𝕜 := ℝ) A⁻¹).det = A⁻¹.det from det_toEuclideanCLM A⁻¹]
  rfl

-- With `A = √S` the flow is `multivariateGaussian b S`, and its density from the flow theorem is
-- the textbook Gaussian density of `multivariateGaussian_eq_withDensity`, almost everywhere.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (b : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosDef) :
    (fun x => ENNReal.ofReal (stdGaussianPDFReal
        (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ (x - b))) *
        ENNReal.ofReal |(CFC.sqrt S)⁻¹.det|) =ᵐ[volume]
      fun x => ENNReal.ofReal (multivariateGaussianPDFReal b S x) := by
  have hU : IsUnit (CFC.sqrt S).det := by
    rw [hS.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact (Real.sqrt_pos.2 hS.det_pos).ne'.isUnit
  have hflow := map_withDensity_eq_withDensity_abs_det_fderiv_symm volume
    (affineEquiv b (CFC.sqrt S) hU) (hasFDerivAt_affineEquiv_symm b (CFC.sqrt S) hU)
    (fun v => ENNReal.ofReal (stdGaussianPDFReal v))
  rw [← stdGaussian_eq_withDensity] at hflow
  have hgauss : multivariateGaussian b S =
      (stdGaussian (EuclideanSpace ℝ ι)).map (affineEquiv b (CFC.sqrt S) hU) := rfl
  rw [← hgauss, multivariateGaussian_eq_withDensity b hS] at hflow
  refine ((withDensity_eq_iff_of_sigmaFinite ?_ ?_).1 ?_).symm
  · exact (ENNReal.measurable_ofReal.comp
      (by unfold multivariateGaussianPDFReal; fun_prop)).aemeasurable
  · exact ((ENNReal.measurable_ofReal.comp (measurable_stdGaussianPDFReal.comp
      ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹).continuous.measurable.comp
        (measurable_id.sub_const b)))).mul_const _).aemeasurable
  · rw [hflow]
    congr 1
    funext x
    rw [show (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹).det = (CFC.sqrt S)⁻¹.det from
      det_toEuclideanCLM _]
    rfl

end ChangeOfVariablesTest

#print axioms map_withDensity_eq_withDensity_abs_det_fderiv_symm
#print axioms map_withDensity_eq_withDensity_abs_det_jacobianMatrix_symm
#print axioms pdf_comp_ae_eq
#print axioms pdf_comp_apply_ae_eq
#print axioms log_pdf_comp_ae
#print axioms log_pdf_comp_apply_ae
#print axioms log_pdf_trans_ae
