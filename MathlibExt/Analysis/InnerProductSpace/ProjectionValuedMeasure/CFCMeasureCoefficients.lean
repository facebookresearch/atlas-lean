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
# Regular scalar measures of continuous functional calculus

Let `T` be a normal bounded operator on a complete complex Hilbert space `H`, with compact
spectrum `K=σ_ℂ(T)`. For `g,h ∈ H`, the bounded complex-linear functional on `C(K,ℂ)` is `f ↦
⟨h,f(T)g⟩`.

Complex Riesz representation gives the unique regular complex measure `μ_(g,h)` satisfying `∫ f
dμ_(g,h)=⟨h,f(T)g⟩` for every continuous `f`. These are scalar measures; a projection-valued
measure is not an input. The zero Hilbert space and empty spectrum are allowed.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped CStarAlgebra InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.ProjectionValuedMeasure
universe uH
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Continuous coefficient functional of a normal operator.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g,h ∈ H`, `normalCFCCoefficientFunctional T hT g h :
C(K,ℂ) →L[ℂ] ℂ` sends `f` to `⟨h,f(T)g⟩`, using continuous functional calculus. -/
def normalCFCCoefficientFunctional (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    C(spectrum ℂ T, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ h).comp ((ContinuousLinearMap.apply ℂ H g).comp
    { toLinearMap := (cfcHom (R := ℂ) hT).toAlgHom.toLinearMap
      cont := cfcHom_continuous (R := ℂ) hT })

/-- **Value of a continuous CFC coefficient.** Let `H` be a complete complex Hilbert space and
`T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with its Borel
measurable structure. for `g,h ∈ H` and `f ∈ C(K,ℂ)`, `normalCFCCoefficientFunctional T hT
g h f=⟨h,cfcHom hT f g⟩=⟨h,f(T)g⟩`. -/
theorem normalCFCCoefficientFunctional_apply (T : H →L[ℂ] H) (hT : IsStarNormal T)
    (g h : H) (f : C(spectrum ℂ T, ℂ)) :
    normalCFCCoefficientFunctional T hT g h f = ⟪h, cfcHom hT f g⟫_ℂ := rfl

/-- **Regular complex Riesz measure of a CFC coefficient.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. for `g,h ∈ H`, `normalCFCCoefficientMeasure T hT g h` is
the regular complex measure `μ_(g,h)` on `K` satisfying `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for every
`f ∈ C(K,ℂ)`. -/
def normalCFCCoefficientMeasure (T : H →L[ℂ] H) (hT : IsStarNormal T) (g h : H) :
    MathlibExt.MeasureTheory.RegularComplexMeasure (spectrum ℂ T) :=
  MathlibExt.MeasureTheory.complexRieszMeasure (normalCFCCoefficientFunctional T hT g h)

/-- **Continuous integral representation of CFC coefficients.** Let `H` be a complete complex
Hilbert space and `T : H →L[ℂ] H` a normal operator, so `T* T=T T*`. Put `K=σ_ℂ(T)` with
its Borel measurable structure. Let `μ_(g,h)` be the regular complex measure on `K`
characterized by `∫ f dμ_(g,h)=⟨h,f(T)g⟩` for `f ∈ C(K,ℂ)`. for `g,h ∈ H` and `f ∈
C(K,ℂ)`, `complexIntegralDual μ_(g,h) f=∫ f dμ_(g,h)=⟨h,f(T)g⟩`. -/
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
