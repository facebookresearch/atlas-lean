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

public import MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure.CFCMeasureProjectionValued

/-!
# Spectral vanishing for the computed normal measure

A continuous spectral function vanishing on a set annihilates that set's
computed spectral projection. The zero spectral projection of an injective
normal operator therefore vanishes, even when zero belongs to its spectrum.
The actual spectrum and Hilbert norm are unchanged; nonmeasurable sets use
the computed zero value.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped CStarAlgebra InnerProductSpace
open MathlibExt.MeasureTheory.Function
open MathlibExt.MeasureTheory.VectorMeasure
namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Let `H` be a complete complex inner product space and let `T : H →L[ℂ] H` be star-normal.
For a subset `s` of the actual spectrum `spectrum ℂ T` and a continuous complex-valued function
`q` on that spectrum, assume `q z = 0` for every `z ∈ s`. Then the continuous functional calculus
value `cfcHom hT q` multiplied by the computed spectral projection `normalCFCPVM T hT s` is zero. -/
theorem normalCFCPVM_cfcHom_mul_eq_zero_of_vanishes
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (s : Set (spectrum ℂ T))
    (q : C(spectrum ℂ T, ℂ)) (hq : ∀ z ∈ s, q z = 0) :
    cfcHom hT q * normalCFCPVM T hT s = 0 := by
  classical
  by_cases hs : MeasurableSet s
  · have hzero : BoundedMeasurableFunction.indicator s hs *
        BoundedMeasurableFunction.ofContinuousMap q = 0 := by
      ext z
      change (BoundedMeasurableFunction.indicator s hs z) * q z = 0
      by_cases hz : z ∈ s
      · rw [hq z hz, mul_zero]
      · rw [BoundedMeasurableFunction.indicator_apply,
          Set.indicator_of_notMem hz, zero_mul]
    have hleft : normalCFCCoefficientOperator T hT s * cfcHom hT q = 0 := by
      apply ContinuousLinearMap.ext
      intro g
      apply ext_inner_left ℂ
      intro h
      change ⟪h, normalCFCCoefficientOperator T hT s (cfcHom hT q g)⟫_ℂ = ⟪h, (0 : H)⟫_ℂ
      rw [inner_zero_right, normalCFCCoefficientOperator_coefficient T hT s hs (cfcHom hT q g) h]
      have hset := normalCFCCoefficientMeasure_cfc_setIntegral T hT g h q s hs
      rw [hzero, complexIntegral_zero] at hset
      exact hset
    have hcomm := normalCFCCoefficientOperator_commute_cfc T hT s q
    change cfcHom hT q * normalCFCCoefficientOperator T hT s = 0
    exact hcomm.eq.symm.trans hleft
  · change cfcHom hT q * normalCFCCoefficientOperator T hT s = 0
    rw [normalCFCCoefficientOperator_not_measurable T hT s hs, mul_zero]

/-- Let `H` be a complete complex inner product space and let the continuous linear
endomorphism `T : H →L[ℂ] H` be star-normal and injective. The value of its computed spectral
measure on `{z : spectrum ℂ T | (z : ℂ) = 0}` is the zero operator on the same Hilbert space `H`. -/
theorem normalCFCPVM_zero_eq_zero_of_injective
    (T : H →L[ℂ] H) (hT : IsStarNormal T) (hInjective : Function.Injective T) :
    normalCFCPVM T hT {z : spectrum ℂ T | (z : ℂ) = 0} = 0 := by
  let q : C(spectrum ℂ T, ℂ) := (ContinuousMap.id ℂ).restrict (spectrum ℂ T)
  have hq : cfcHom hT q = T := cfcHom_id hT
  have hproduct : T * normalCFCPVM T hT {z : spectrum ℂ T | (z : ℂ) = 0} = 0 := by
    have hzero := normalCFCPVM_cfcHom_mul_eq_zero_of_vanishes T hT
      {z : spectrum ℂ T | (z : ℂ) = 0} q (by intro z hz; exact hz)
    simpa only [hq] using hzero
  apply ContinuousLinearMap.ext
  intro x
  apply hInjective
  have hx := congrArg (fun A : H →L[ℂ] H => A x) hproduct
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero] using hx

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure

end
