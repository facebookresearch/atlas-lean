/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.WhittakerExpansion

@[expose] public section

open IsDedekindDomain NumberField AutomorphicForm

/-- The Whittaker expansion with the original binders. -/
private theorem exactSource
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)) :
    HasSum (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)
      (φ g) :=
  AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ g hcont hsum

-- The expansion in a higher universe.
example
    (F : Type 1) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)) :
    HasSum (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (NumberField.AdelicBox.adelicBox F)) ψ φ α g)
      (φ g) :=
  AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ g hcont hsum

-- Importing the Whittaker expansion keeps Mathlib's measurable-space instance on quotients:
-- the instance removal in `WhittakerExpansion` is local to its section.
example {α : Type*} [MeasurableSpace α] (s : Setoid α) :
    (inferInstance : MeasurableSpace (Quotient s)) = Quotient.instMeasurableSpace := rfl

-- Boundary example: the summability hypothesis matters. For the zero
-- function every coefficient vanishes, and the expansion is the empty sum;
-- the constant-term coefficient of a nonzero constant function is that
-- constant, showing the `α = 0` coefficient is the constant term.
example (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 :=
  whittakerCoefficient_zero F pins ψ α g

example (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g :=
  whittakerCoefficient_zero_eq_constantTerm F pins ψ φ g

-- The Whittaker coefficient is the adelic Fourier integral of `x ↦ φ (unipotentGL2 x * g)`.
example (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α g
      = @NumberField.AdelicFourier.fourierIntegral _ _ pins.nS ψ pins.ν
          (fun x => φ (unipotentGL2 x * g)) (algebraMap F (AdeleRing (𝓞 F) F) α) :=
  rfl

-- Cuspidality requires integrable constant-term integrands. A nonzero constant against
-- Lebesgue measure on `ℝ` has vanishing constant terms, because the Bochner integral of a
-- non-integrable function is zero, but it is not cuspidal; the zero function is cuspidal.
open MeasureTheory in
example : (∀ g, constantTerm (volume : Measure ℝ) (Multiplicative.ofAdd : ℝ → Multiplicative ℝ)
      (fun _ => (1 : ℂ)) g = 0) ∧
    ¬ IsCuspidalFn (volume : Measure ℝ) (Multiplicative.ofAdd : ℝ → Multiplicative ℝ)
      (fun _ => (1 : ℂ)) := by
  have hni : ¬ Integrable (fun _ : ℝ => (1 : ℂ)) (volume : Measure ℝ) := by
    rw [integrable_const_iff, not_or, not_isFiniteMeasure_iff, Real.volume_univ]
    exact ⟨one_ne_zero, rfl⟩
  exact ⟨fun g => integral_undef hni, fun h => hni (h 1).1⟩

open MeasureTheory in
example {Q G : Type} [MeasurableSpace Q] [Group G] (μ : Measure Q) (u : Q → G) :
    IsCuspidalFn μ u (fun _ => (0 : ℂ)) :=
  fun g => ⟨integrable_zero _ _ μ, constantTerm_zero μ u g⟩
