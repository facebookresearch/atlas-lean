/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Probability.Density
public import MathlibExt.Analysis.Calculus.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Densities under a change of variables (normalizing flows)

Let `T : E ≃ᵐ E` be a measurable equivalence of a finite-dimensional real vector space whose
inverse is differentiable, with derivative `S' x` at `x`, and let `μ` be an additive Haar measure,
such as Lebesgue measure. If `Z` has density `p` with respect to `μ`, then `X = T Z` has density
`x ↦ p (T⁻¹ x) * |det S' x|`. This is the change-of-variables identity behind normalizing flows
(D. J. Rezende and S. Mohamed, *Variational Inference with Normalizing Flows*, ICML 2015, §3.1;
G. Papamakarios et al., *Normalizing Flows for Probabilistic Modeling and Inference*, JMLR 22
(2021), §2.1). It is Mathlib's change-of-variables formula
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` applied to `T⁻¹`.

Main results:

* `map_withDensity_eq_withDensity_abs_det_fderiv_symm`: the identity of measures
  `(μ.withDensity p).map T = μ.withDensity (fun x ↦ p (T⁻¹ x) * |det S' x|)`, for every `p`.
* `map_withDensity_eq_withDensity_abs_det_jacobianMatrix_symm`: the same on `Fin d → ℝ`, with the
  determinant of the coordinate Jacobian matrix `jacobianMatrix`.
* `pdf_comp_ae_eq`, `pdf_comp_apply_ae_eq`: the identity for Mathlib's `pdf`, in the inverse form
  `p_X x = p_Z (T⁻¹ x) * |det D(T⁻¹)(x)|` and the forward form `p_X (T z) = p_Z z / |det DT(z)|`.
* `log_pdf_comp_ae`, `log_pdf_comp_apply_ae`: the log-likelihood identities
  `log p_X x = log p_Z (T⁻¹ x) + log |det D(T⁻¹)(x)|` and
  `log p_X (T z) = log p_Z z - log |det DT(z)|`, almost everywhere.
* `log_pdf_trans_ae`: for a composite flow the log-determinants of the layers add.

The density identities hold for every density. The logarithmic identities use the real logarithm
and assume the base density is positive and finite at the point (and, in the inverse form, that the
Jacobian determinant is nonzero): Lean's conventions `Real.log 0 = 0` and `ENNReal.toReal ⊤ = 0`
make them false otherwise.
-/

public section

namespace MetaMathlibExt

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Change of variables for densities.** If `T` is a measurable equivalence whose inverse has
derivative `S' x` at every `x`, the image under `T` of the measure with density `p` has density
`x ↦ p (T⁻¹ x) * |det S' x|`. No measurability of `p` and no invertibility of `S' x` is needed. -/
theorem map_withDensity_eq_withDensity_abs_det_fderiv_symm (T : E ≃ᵐ E)
    {S' : E → E →L[ℝ] E} (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (p : E → ℝ≥0∞) :
    (μ.withDensity p).map T =
      μ.withDensity fun x => p (T.symm x) * ENNReal.ofReal |(S' x).det| := by
  ext t ht
  rw [Measure.map_apply T.measurable ht, withDensity_apply _ (T.measurable ht),
    withDensity_apply _ ht, ← T.image_symm,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht
      (fun x _ => (hS' x).hasFDerivWithinAt) T.symm.injective.injOn p]
  simp_rw [mul_comm]

/-- The coordinate form of `map_withDensity_eq_withDensity_abs_det_fderiv_symm` on `Fin d → ℝ`:
the density of the image is `x ↦ p (T⁻¹ x) * |det J_{T⁻¹}(x)|`, with `J` the Jacobian matrix. -/
theorem map_withDensity_eq_withDensity_abs_det_jacobianMatrix_symm {d : ℕ}
    (T : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ)) (hT : Differentiable ℝ T.symm)
    (p : (Fin d → ℝ) → ℝ≥0∞) :
    (volume.withDensity p).map T =
      volume.withDensity fun x =>
        p (T.symm x) * ENNReal.ofReal |(jacobianMatrix T.symm x).det| := by
  rw [map_withDensity_eq_withDensity_abs_det_fderiv_symm volume T
    (fun x => (hT x).hasFDerivAt) p]
  congr 1
  funext x
  rw [jacobianMatrix_eq_toMatrix'_fderiv _ x (hT x), LinearMap.det_toMatrix']

/-- A measurable equivalence with a differentiable inverse is quasi-measure-preserving for a Haar
measure: the preimage under `T` of a null set is the image of a null set under `T⁻¹`, hence null. -/
theorem quasiMeasurePreserving_of_differentiable_symm (T : E ≃ᵐ E)
    (hT : Differentiable ℝ T.symm) : QuasiMeasurePreserving T μ μ := by
  refine ⟨T.measurable.aemeasurable, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply T.measurable hs, ← T.image_symm]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hT.differentiableOn hs0

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- If `T` has derivative `A` at `z` and `T⁻¹` has derivative `B` at `T z`, then
`det B * det A = 1`. The theorem does not assume `FiniteDimensional ℝ E`; on an
infinite-dimensional `E` the determinant (`LinearMap.det`) is `1`, so the statement is trivial
there. -/
theorem det_fderiv_symm_mul_det_fderiv (T : E ≃ᵐ E) {A B : E →L[ℝ] E} {z : E}
    (hT : HasFDerivAt T A z) (hS : HasFDerivAt T.symm B (T z)) : B.det * A.det = 1 := by
  have hcomp : HasFDerivAt (T.symm ∘ T) (B.comp A) z := HasFDerivAt.comp z hS hT
  rw [T.symm_comp_self] at hcomp
  have hid : B.comp A = ContinuousLinearMap.id ℝ E := hcomp.unique (hasFDerivAt_id z)
  have hcoe : ((B.comp A : E →L[ℝ] E) : E →ₗ[ℝ] E) = (B : E →ₗ[ℝ] E) ∘ₗ (A : E →ₗ[ℝ] E) := rfl
  change LinearMap.det (B : E →ₗ[ℝ] E) * LinearMap.det (A : E →ₗ[ℝ] E) = 1
  rw [← LinearMap.det_comp, ← hcoe, hid, ContinuousLinearMap.coe_id, LinearMap.det_id]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The law of `T ∘ Z` has density `x ↦ pdf Z (T⁻¹ x) * |det S' x|`. -/
theorem map_comp_eq_withDensity (T : E ≃ᵐ E) {S' : E → E →L[ℝ] E}
    (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    ℙ.map (T ∘ Z) =
      μ.withDensity fun x => pdf Z ℙ μ (T.symm x) * ENNReal.ofReal |(S' x).det| := by
  rw [← AEMeasurable.map_map_of_aemeasurable T.measurable.aemeasurable
    (HasPDF.aemeasurable Z ℙ μ), map_eq_withDensity_pdf Z ℙ μ,
    map_withDensity_eq_withDensity_abs_det_fderiv_symm μ T hS']

/-- The function `x ↦ pdf Z (T⁻¹ x) * |det S' x|` is almost everywhere measurable. Here
`pdf Z ℙ μ` is Mathlib's Radon-Nikodym derivative of the law of `Z` with respect to `μ`: the
density of its absolutely continuous part, and `0` when the law has no Lebesgue decomposition
with respect to `μ`. -/
theorem aemeasurable_pdf_comp_symm_mul_abs_det (T : E ≃ᵐ E) {S' : E → E →L[ℝ] E}
    (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (Z : Ω → E) (ℙ : Measure Ω) :
    AEMeasurable (fun x => pdf Z ℙ μ (T.symm x) * ENNReal.ofReal |(S' x).det|) μ := by
  have hJ := aemeasurable_ofReal_abs_det_fderivWithin μ MeasurableSet.univ
    (fun x _ => (hS' x).hasFDerivWithinAt)
  rw [Measure.restrict_univ] at hJ
  exact ((measurable_pdf Z ℙ μ).comp T.symm.measurable).aemeasurable.mul hJ

/-- If `Z` has a density, so does `T ∘ Z`. -/
theorem hasPDF_comp (T : E ≃ᵐ E) {S' : E → E →L[ℝ] E}
    (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    HasPDF (T ∘ Z) ℙ μ :=
  hasPDF_of_map_eq_withDensity (T.measurable.comp_aemeasurable (HasPDF.aemeasurable Z ℙ μ)) _
    (aemeasurable_pdf_comp_symm_mul_abs_det μ T hS' Z ℙ) (map_comp_eq_withDensity μ T hS' Z ℙ)

/-- **Density of a normalizing flow, inverse form.** `p_X x = p_Z (T⁻¹ x) * |det D(T⁻¹)(x)|`
for almost every `x`, where `X = T ∘ Z`. -/
theorem pdf_comp_ae_eq (T : E ≃ᵐ E) {S' : E → E →L[ℝ] E}
    (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    pdf (T ∘ Z) ℙ μ =ᵐ[μ] fun x => pdf Z ℙ μ (T.symm x) * ENNReal.ofReal |(S' x).det| := by
  have := hasPDF_comp μ T hS' Z ℙ
  exact (pdf.eq_of_map_eq_withDensity' (X := T ∘ Z) _
    (aemeasurable_pdf_comp_symm_mul_abs_det μ T hS' Z ℙ)).1 (map_comp_eq_withDensity μ T hS' Z ℙ)

/-- **Density of a normalizing flow, forward form.** If `T` also has derivative `T' z` at every
`z`, then `p_X (T z) = p_Z z * |det DT(z)|⁻¹` for almost every `z`, where `X = T ∘ Z`. -/
theorem pdf_comp_apply_ae_eq (T : E ≃ᵐ E) {T' S' : E → E →L[ℝ] E}
    (hT' : ∀ z, HasFDerivAt T (T' z) z) (hS' : ∀ x, HasFDerivAt T.symm (S' x) x)
    (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    ∀ᵐ z ∂μ, pdf (T ∘ Z) ℙ μ (T z) = pdf Z ℙ μ z * ENNReal.ofReal |(T' z).det|⁻¹ := by
  filter_upwards [(quasiMeasurePreserving_of_differentiable_symm μ T
    fun x => (hS' x).differentiableAt).ae (pdf_comp_ae_eq μ T hS' Z ℙ)] with z hz
  rw [hz, T.symm_apply_apply, ← abs_inv, ← eq_inv_of_mul_eq_one_left
    (det_fderiv_symm_mul_det_fderiv T (hT' z) (hS' (T z)))]

/-- **Log-likelihood of a normalizing flow, inverse form.** For almost every `x`, if the base
density at `T⁻¹ x` is positive and finite and `det D(T⁻¹)(x) ≠ 0`, then
`log p_X x = log p_Z (T⁻¹ x) + log |det D(T⁻¹)(x)|`, where `X = T ∘ Z`. -/
theorem log_pdf_comp_ae (T : E ≃ᵐ E) {S' : E → E →L[ℝ] E}
    (hS' : ∀ x, HasFDerivAt T.symm (S' x) x) (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    ∀ᵐ x ∂μ, pdf Z ℙ μ (T.symm x) ≠ 0 → pdf Z ℙ μ (T.symm x) ≠ ∞ → (S' x).det ≠ 0 →
      Real.log (pdf (T ∘ Z) ℙ μ x).toReal =
        Real.log (pdf Z ℙ μ (T.symm x)).toReal + Real.log |(S' x).det| := by
  filter_upwards [pdf_comp_ae_eq μ T hS' Z ℙ] with x hx h0 htop hdet
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    Real.log_mul (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩) (abs_ne_zero.2 hdet)]

/-- **Log-likelihood of a normalizing flow, forward form.** If `T` also has derivative `T' z` at
every `z`, then for almost every `z` at which the base density is positive and finite,
`log p_X (T z) = log p_Z z - log |det DT(z)|`, where `X = T ∘ Z`. -/
theorem log_pdf_comp_apply_ae (T : E ≃ᵐ E) {T' S' : E → E →L[ℝ] E}
    (hT' : ∀ z, HasFDerivAt T (T' z) z) (hS' : ∀ x, HasFDerivAt T.symm (S' x) x)
    (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    ∀ᵐ z ∂μ, pdf Z ℙ μ z ≠ 0 → pdf Z ℙ μ z ≠ ∞ →
      Real.log (pdf (T ∘ Z) ℙ μ (T z)).toReal =
        Real.log (pdf Z ℙ μ z).toReal - Real.log |(T' z).det| := by
  filter_upwards [pdf_comp_apply_ae_eq μ T hT' hS' Z ℙ] with z hz h0 htop
  have hdet : (T' z).det ≠ 0 :=
    right_ne_zero_of_mul_eq_one (det_fderiv_symm_mul_det_fderiv T (hT' z) (hS' (T z)))
  rw [hz, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg _)),
    Real.log_mul (ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩)
      (inv_ne_zero (abs_ne_zero.2 hdet)), Real.log_inv, sub_eq_add_neg]

/-- **Composition adds log-determinants.** For the two-layer flow `T₂ ∘ T₁` with inverse
derivatives `S₁'` and `S₂'`, almost everywhere where the base density is positive and finite and
both determinants are nonzero,
`log p_X x = log p_Z (T₁⁻¹ (T₂⁻¹ x)) + log |det S₁' (T₂⁻¹ x)| + log |det S₂' x|`. -/
theorem log_pdf_trans_ae (T₁ T₂ : E ≃ᵐ E) {S₁' S₂' : E → E →L[ℝ] E}
    (hS₁' : ∀ x, HasFDerivAt T₁.symm (S₁' x) x) (hS₂' : ∀ x, HasFDerivAt T₂.symm (S₂' x) x)
    (Z : Ω → E) (ℙ : Measure Ω) [HasPDF Z ℙ μ] :
    ∀ᵐ x ∂μ, pdf Z ℙ μ (T₁.symm (T₂.symm x)) ≠ 0 → pdf Z ℙ μ (T₁.symm (T₂.symm x)) ≠ ∞ →
      (S₁' (T₂.symm x)).det ≠ 0 → (S₂' x).det ≠ 0 →
      Real.log (pdf (T₂ ∘ T₁ ∘ Z) ℙ μ x).toReal =
        Real.log (pdf Z ℙ μ (T₁.symm (T₂.symm x))).toReal +
          Real.log |(S₁' (T₂.symm x)).det| + Real.log |(S₂' x).det| := by
  have hS' : ∀ x, HasFDerivAt (T₁.trans T₂).symm ((S₁' (T₂.symm x)).comp (S₂' x)) x := by
    intro x
    rw [MeasurableEquiv.trans_symm, MeasurableEquiv.coe_trans]
    exact HasFDerivAt.comp x (hS₁' (T₂.symm x)) (hS₂' x)
  filter_upwards [log_pdf_comp_ae μ (T₁.trans T₂) hS' Z ℙ] with x hx h0 htop h₁ h₂
  have hdet : ((S₁' (T₂.symm x)).comp (S₂' x)).det =
      (S₁' (T₂.symm x)).det * (S₂' x).det := by
    change LinearMap.det ((S₁' (T₂.symm x) : E →ₗ[ℝ] E) ∘ₗ (S₂' x : E →ₗ[ℝ] E)) = _
    exact LinearMap.det_comp _ _
  have h := hx h0 htop (by rw [hdet]; exact mul_ne_zero h₁ h₂)
  rw [hdet, abs_mul, Real.log_mul (abs_ne_zero.2 h₁) (abs_ne_zero.2 h₂), ← add_assoc] at h
  exact h

end MetaMathlibExt
