/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.BruhatEisenstein

@[expose] public section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped NNReal

namespace AutomorphicFormBruhatEisensteinTest

/-- `exactSource` consumer with the original binders. -/
public theorem exactSource
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g :=
  fun hα μ ν hμ hν _s hs _φ hφ hφc g =>
    constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F μ ν hα hμ hν hs hφ
      hφc g

/-- `exactSource` consumer for the integrability input, with the original binders. -/
public theorem exactSourceIntegrable
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    Integrable (fun x : AdeleRing (𝓞 F) F =>
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) :=
  fun hα μ ν hμ hν _s hs _φ hφ hφc g =>
    weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν hs hφ hφc g

attribute [local instance] NumberField.AdelicHaar.adeleBorel

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne (F : Type 1) [Field F] [NumberField F]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hα : ∀ x, 0 < (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ))
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F
      (etaFst μ ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits hα s)
      (etaSnd ν ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits hα s) φ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        unipotentGL2 (bruhatEisenstein (𝓞 F) F φ) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g :=
  constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F μ ν hα hμ hν hs hφ
    hφc g

/-- The positivity hypothesis on the Haar modulus always holds: the modulus is a character of
a group, so it never vanishes. -/
public theorem distribHaarChar_pos (F : Type*) [Field F] [NumberField F]
    (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) := by
  have h : distribHaarChar (AdeleRing (𝓞 F) F) x *
      distribHaarChar (AdeleRing (𝓞 F) F) x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h))

/-- The Bruhat sum of the zero section vanishes identically. -/
public example (F : Type*) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    bruhatEisenstein (𝓞 F) F (fun _ => (0 : ℂ)) g = 0 := by
  simp [bruhatEisenstein_apply]

end AutomorphicFormBruhatEisensteinTest
