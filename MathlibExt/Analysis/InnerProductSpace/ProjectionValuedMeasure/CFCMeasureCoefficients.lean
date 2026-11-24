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

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import MathlibExt.MeasureTheory.Integral.RieszMarkovKakutani.Complex

/-!
# Strict scalar Riesz coefficients of the actual normal-operator CFC

These defining values serve the missing canonical normal-operator PVM
constructor required by Murphy resolutionOfIdentity. The coefficient
functional is built from the actual continuous functional calculus, ordinary
operator evaluation and innerSL; the representing regular complex measure
comes from the existing strict complex Riesz map. No spectral PVM, correctness
certificate, chosen representation or terminal source theorem is an input.
This module constructs scalar coefficients only; projection/intersection and
strong countable-additivity proofs are still required to bundle a PVM.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original normal CFC matrix-coefficient functional, with the same
orientation as scalarMeasure g h: f maps to inner h ((cfcHom hT f) g). -/
def normalCFCCoefficientFunctional (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    C(spectrum ℂ T, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ h).comp ((ContinuousLinearMap.apply ℂ H g).comp
    { toLinearMap := (cfcHom (R := ℂ) hT).toAlgHom.toLinearMap
      cont := cfcHom_continuous (R := ℂ) hT })

/-- The coefficient uses the actual stock CFC and original Hilbert inner product. -/
theorem normalCFCCoefficientFunctional_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f : C(spectrum ℂ T, ℂ)) :
    normalCFCCoefficientFunctional T hT g h f = ⟪h, cfcHom hT f g⟫_ℂ := rfl

/-- The existing strict complex-Riesz constructor supplies the actual regular
measure of this same CFC coefficient; it is not yet a projection-valued measure. -/
def normalCFCCoefficientMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    MathlibExt.MeasureTheory.RegularComplexMeasure (spectrum ℂ T) :=
  MathlibExt.MeasureTheory.complexRieszMeasure (normalCFCCoefficientFunctional T hT g h)

/-- The original regular coefficient measure represents every continuous CFC value. -/
theorem normalCFCCoefficientMeasure_represents (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f : C(spectrum ℂ T, ℂ)) :
    MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) f =
      ⟪h, cfcHom hT f g⟫_ℂ := by
  have hRiesz := MathlibExt.MeasureTheory.complexIntegralDual_complexRieszMeasure
    (normalCFCCoefficientFunctional T hT g h)
  have hvalue := congrArg (fun L : StrongDual ℂ C(spectrum ℂ T, ℂ) => L f) hRiesz
  change MathlibExt.MeasureTheory.complexIntegralDual (normalCFCCoefficientMeasure T hT g h) f =
    normalCFCCoefficientFunctional T hT g h f at hvalue
  exact hvalue.trans (normalCFCCoefficientFunctional_apply T hT g h f)

end MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
