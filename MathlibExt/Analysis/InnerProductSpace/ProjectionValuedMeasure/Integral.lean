/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.ScalarMeasure
public import MathlibExt.MeasureTheory.VectorMeasure.ComplexIntegral
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Spectral integration for projection-valued measures

This file constructs the bounded operator integral of a bounded measurable
complex-valued function against a projection-valued measure.  The construction
is characterized by its scalar coefficients and agrees with the canonical
finite sum on measurable simple functions.  It also provides the contraction,
Lipschitz, strict simple-function approximation, and uniqueness interfaces
needed for the later algebraic extension.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace NNReal

open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure

namespace MathlibExt.Analysis.InnerProductSpace
namespace ProjectionValuedMeasure

noncomputable section

universe u v

variable {X : Type u} {H : Type v}
variable [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def spectralIntegralFormLinear
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun h :=
    { toFun := fun g ↦ complexIntegral (E.scalarMeasure g h) phi
      map_add' := by
        intro g₁ g₂
        rw [E.scalarMeasure_add_left, complexIntegral_add_measure]
      map_smul' := by
        intro c g
        rw [E.scalarMeasure_smul_left, complexIntegral_smul_measure]
        rfl }
  map_add' := by
    intro h₁ h₂
    ext g
    change complexIntegral (E.scalarMeasure g (h₁ + h₂)) phi =
      complexIntegral (E.scalarMeasure g h₁) phi + complexIntegral (E.scalarMeasure g h₂) phi
    rw [E.scalarMeasure_add_right, complexIntegral_add_measure]
  map_smul' := by
    intro c h
    ext g
    change complexIntegral (E.scalarMeasure g (c • h)) phi =
      star c • complexIntegral (E.scalarMeasure g h) phi
    rw [E.scalarMeasure_smul_right, complexIntegral_smul_measure]

private theorem norm_spectralIntegralFormLinear_apply_le
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) (h g : H) :
    ‖spectralIntegralFormLinear E phi h g‖ ≤ ‖phi‖ * ‖h‖ * ‖g‖ := by
  calc
    ‖spectralIntegralFormLinear E phi h g‖ =
        ‖complexIntegral (E.scalarMeasure g h) phi‖ := rfl
    _ ≤ ‖phi‖ * (E.scalarMeasure g h).variation.real Set.univ :=
      norm_complexIntegral_le (E.scalarMeasure g h) phi
    _ ≤ ‖phi‖ * (‖g‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left (E.scalarMeasure_variation_real_univ_le g h)
        (norm_nonneg phi)
    _ = ‖phi‖ * ‖h‖ * ‖g‖ := by ring

/-- The bounded sesquilinear coefficient form of the spectral integral.  It is
conjugate-linear in the first vector and linear in the second. -/
@[no_expose]
noncomputable def spectralIntegralForm
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (spectralIntegralFormLinear E phi) ‖phi‖
    (norm_spectralIntegralFormLinear_apply_le E phi)

@[simp]
theorem spectralIntegralForm_apply
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) (h g : H) :
    spectralIntegralForm E phi h g = complexIntegral (E.scalarMeasure g h) phi := by
  simp [spectralIntegralForm, spectralIntegralFormLinear]

/-- The bounded operator integral of `phi` against `E`.  The adjoint is required
because Mathlib's inner product is conjugate-linear in its first argument. -/
@[no_expose]
noncomputable def spectralIntegral
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    H →L[ℂ] H :=
  (InnerProductSpace.continuousLinearMapOfBilin (spectralIntegralForm E phi)).adjoint

/-- Characteristic scalar-coefficient identity for the spectral integral. -/
theorem inner_spectralIntegral_apply
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) (g h : H) :
    ⟪h, spectralIntegral E phi g⟫_ℂ = complexIntegral (E.scalarMeasure g h) phi := by
  rw [spectralIntegral]
  calc
    ⟪h, (InnerProductSpace.continuousLinearMapOfBilin
          (spectralIntegralForm E phi)).adjoint g⟫_ℂ =
        ⟪InnerProductSpace.continuousLinearMapOfBilin (spectralIntegralForm E phi) h, g⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = spectralIntegralForm E phi h g :=
      InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
    _ = complexIntegral (E.scalarMeasure g h) phi :=
      spectralIntegralForm_apply E phi h g

private theorem norm_spectralIntegral_apply_le
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) (g : H) :
    ‖spectralIntegral E phi g‖ ≤ ‖phi‖ * ‖g‖ := by
  by_cases hg : spectralIntegral E phi g = 0
  · rw [hg, norm_zero]
    positivity
  · have hpos : 0 < ‖spectralIntegral E phi g‖ := norm_pos_iff.mpr hg
    have hbound :
        ‖spectralIntegral E phi g‖ * ‖spectralIntegral E phi g‖ ≤
          (‖phi‖ * ‖g‖) * ‖spectralIntegral E phi g‖ := calc
      ‖spectralIntegral E phi g‖ * ‖spectralIntegral E phi g‖ =
          ‖⟪spectralIntegral E phi g, spectralIntegral E phi g⟫_ℂ‖ := by
        rw [inner_self_eq_norm_sq_to_K]
        simp [pow_two]
      _ = ‖complexIntegral
          (E.scalarMeasure g (spectralIntegral E phi g)) phi‖ := by
        rw [inner_spectralIntegral_apply]
      _ ≤ ‖phi‖ *
          (E.scalarMeasure g (spectralIntegral E phi g)).variation.real Set.univ :=
        norm_complexIntegral_le _ _
      _ ≤ ‖phi‖ * (‖g‖ * ‖spectralIntegral E phi g‖) :=
        mul_le_mul_of_nonneg_left
          (E.scalarMeasure_variation_real_univ_le g (spectralIntegral E phi g))
          (norm_nonneg phi)
      _ = (‖phi‖ * ‖g‖) * ‖spectralIntegral E phi g‖ := by ring
    nlinarith

/-- Spectral integration is contractive for the supremum norm. -/
theorem norm_spectralIntegral_le
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    ‖spectralIntegral E phi‖ ≤ ‖phi‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg phi)
  exact norm_spectralIntegral_apply_le E phi

theorem spectralIntegral_add
    (E : ProjectionValuedMeasure X H) (phi psi : BoundedMeasurableFunction X) :
    spectralIntegral E (phi + psi) = spectralIntegral E phi + spectralIntegral E psi := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  simp only [inner_spectralIntegral_apply, add_apply, inner_add_right,
    complexIntegral_add]

theorem spectralIntegral_smul
    (E : ProjectionValuedMeasure X H) (c : ℂ) (phi : BoundedMeasurableFunction X) :
    spectralIntegral E (c • phi) = c • spectralIntegral E phi := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  simp only [inner_spectralIntegral_apply, smul_apply, inner_smul_right,
    complexIntegral_smul, smul_eq_mul]

/-- Spectral integration as a contraction between normed complex spaces. -/
@[no_expose]
noncomputable def spectralIntegralCLM (E : ProjectionValuedMeasure X H) :
    BoundedMeasurableFunction X →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := spectralIntegral E
      map_add' := by
        intro phi psi
        exact spectralIntegral_add E phi psi
      map_smul' := by
        intro c phi
        exact spectralIntegral_smul E c phi }
    1
    (fun phi ↦ by simpa using norm_spectralIntegral_le E phi)

@[simp]
theorem spectralIntegralCLM_apply
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X) :
    spectralIntegralCLM E phi = spectralIntegral E phi := by
  simp [spectralIntegralCLM]

/-- Difference form of the contraction estimate. -/
theorem norm_spectralIntegral_sub_le
    (E : ProjectionValuedMeasure X H) (phi psi : BoundedMeasurableFunction X) :
    ‖spectralIntegral E phi - spectralIntegral E psi‖ ≤ ‖phi - psi‖ := by
  calc
    ‖spectralIntegral E phi - spectralIntegral E psi‖ =
        ‖spectralIntegralCLM E phi - spectralIntegralCLM E psi‖ := by
      rw [spectralIntegralCLM_apply, spectralIntegralCLM_apply]
    _ = ‖spectralIntegralCLM E (phi - psi)‖ := by
      let F : BoundedMeasurableFunction X →L[ℂ] (H →L[ℂ] H) := spectralIntegralCLM E
      have hsub : F (phi - psi) = F phi - F psi := F.map_sub phi psi
      exact congrArg (fun T : H →L[ℂ] H => ‖T‖) hsub.symm
    _ = ‖spectralIntegral E (phi - psi)‖ := by rw [spectralIntegralCLM_apply]
    _ ≤ ‖phi - psi‖ := norm_spectralIntegral_le E (phi - psi)

/-- Metric form of the contraction estimate. -/
theorem dist_spectralIntegral_le
    (E : ProjectionValuedMeasure X H) (phi psi : BoundedMeasurableFunction X) :
    dist (spectralIntegral E phi) (spectralIntegral E psi) ≤ dist phi psi := by
  calc
    dist (spectralIntegral E phi) (spectralIntegral E psi) =
        ‖spectralIntegral E phi - spectralIntegral E psi‖ := dist_eq_norm _ _
    _ ≤ ‖phi - psi‖ := norm_spectralIntegral_sub_le E phi psi
    _ = dist phi psi := (dist_eq_norm phi psi).symm

/-- The canonical finite operator sum attached to a measurable simple
function. -/
noncomputable def simpleSpectralIntegral
    (E : ProjectionValuedMeasure X H) (f : SimpleFunc X ℂ) : H →L[ℂ] H :=
  ∑ c ∈ f.range, c • E (f ⁻¹' {c})

/-- Spectral integration agrees with the canonical finite sum on measurable
simple functions. -/
theorem spectralIntegral_ofSimpleFunc
    (E : ProjectionValuedMeasure X H) (f : SimpleFunc X ℂ) :
    spectralIntegral E (BoundedMeasurableFunction.ofSimpleFunc f) =
      simpleSpectralIntegral E f := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [inner_spectralIntegral_apply, complexIntegral_ofSimpleFunc]
  rw [simpleSpectralIntegral]
  simp only [ProjectionValuedMeasure.scalarMeasure_apply, sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [smul_apply, inner_smul_right]

/-- Integral of a constant-valued measurable indicator. -/
theorem spectralIntegral_indicatorConst
    (E : ProjectionValuedMeasure X H) (s : Set X) (hs : MeasurableSet s) (c : ℂ) :
    spectralIntegral E (BoundedMeasurableFunction.indicatorConst s hs c) = c • E s := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro h
  rw [inner_spectralIntegral_apply, complexIntegral_indicatorConst,
    ProjectionValuedMeasure.scalarMeasure_apply]
  change c * ⟪h, E s g⟫_ℂ = ⟪h, c • E s g⟫_ℂ
  rw [inner_smul_right]

/-- Integral of a measurable characteristic function. -/
theorem spectralIntegral_indicator
    (E : ProjectionValuedMeasure X H) (s : Set X) (hs : MeasurableSet s) :
    spectralIntegral E (BoundedMeasurableFunction.indicator s hs) = E s := by
  simpa [BoundedMeasurableFunction.indicator] using
    spectralIntegral_indicatorConst E s hs (1 : ℂ)

/-- A uniform simple approximation with margin `delta < epsilon` gives the
strict operator-norm estimate required by the finite-partition construction. -/
theorem norm_spectralIntegral_sub_simpleSpectralIntegral_lt
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X)
    (f : SimpleFunc X ℂ) {delta epsilon : ℝ} (hdelta : 0 ≤ delta)
    (hdeltaepsilon : delta < epsilon)
    (happrox : ∀ x, ‖phi x - f x‖ ≤ delta) :
    ‖spectralIntegral E phi - simpleSpectralIntegral E f‖ < epsilon := by
  have hnorm : ‖phi - BoundedMeasurableFunction.ofSimpleFunc f‖ ≤ delta := by
    change ‖(phi - BoundedMeasurableFunction.ofSimpleFunc f).toLp‖ ≤ delta
    apply lp.norm_le_of_forall_le hdelta
    intro x
    change ‖phi x - BoundedMeasurableFunction.ofSimpleFunc f x‖ ≤ delta
    simpa only [BoundedMeasurableFunction.ofSimpleFunc_apply] using happrox x
  rw [← spectralIntegral_ofSimpleFunc E f]
  exact (norm_spectralIntegral_sub_le E phi
    (BoundedMeasurableFunction.ofSimpleFunc f)).trans_lt
      (hnorm.trans_lt hdeltaepsilon)

/-- Every spectral integral is a strict operator-norm limit of canonical
finite simple-function sums. -/
theorem exists_simpleSpectralIntegral_norm_sub_lt
    (E : ProjectionValuedMeasure X H) (phi : BoundedMeasurableFunction X)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ f : SimpleFunc X ℂ,
      ‖spectralIntegral E phi - simpleSpectralIntegral E f‖ < epsilon := by
  obtain ⟨f, hf⟩ := BoundedMeasurableFunction.exists_simpleFunc_norm_sub_lt phi hepsilon
  refine ⟨f, ?_⟩
  rw [← spectralIntegral_ofSimpleFunc E f]
  exact (norm_spectralIntegral_sub_le E phi
    (BoundedMeasurableFunction.ofSimpleFunc f)).trans_lt hf

private theorem dense_range_ofSimpleFunc :
    Dense (Set.range (BoundedMeasurableFunction.ofSimpleFunc :
      SimpleFunc X ℂ → BoundedMeasurableFunction X)) := by
  rw [Metric.dense_iff]
  intro phi epsilon hepsilon
  obtain ⟨f, hf⟩ := BoundedMeasurableFunction.exists_simpleFunc_norm_sub_lt phi hepsilon
  refine ⟨BoundedMeasurableFunction.ofSimpleFunc f, ?_, ⟨f, rfl⟩⟩
  simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hf

/-- The coefficient construction is the unique continuous linear extension of
the canonical simple-function sums. -/
theorem spectralIntegralCLM_unique
    (E : ProjectionValuedMeasure X H)
    (T : BoundedMeasurableFunction X →L[ℂ] (H →L[ℂ] H))
    (hT : ∀ f : SimpleFunc X ℂ,
      T (BoundedMeasurableFunction.ofSimpleFunc f) = simpleSpectralIntegral E f) :
    T = spectralIntegralCLM E := by
  apply ContinuousLinearMap.ext_on
    (dense_range_ofSimpleFunc (X := X) |>.mono Submodule.subset_span)
  rintro _ ⟨f, rfl⟩
  rw [hT f, spectralIntegralCLM_apply, spectralIntegral_ofSimpleFunc]

end

end ProjectionValuedMeasure
end MathlibExt.Analysis.InnerProductSpace
