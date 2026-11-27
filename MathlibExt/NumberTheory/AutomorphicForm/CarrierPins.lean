/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_CarrierPins.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.FnTwist
public import MathlibExt.NumberTheory.NumberField.AdelicHaar

@[expose] public section

open IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory

noncomputable section

namespace AutomorphicForm

/-- The carrier data (measurable-space and measure pins, a domain, a central
subgroup, level subgroups and generators) used to form adelic integrals. -/
public structure CarrierPins (F : Type*) [Field F] [NumberField F] where
  mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)
  μ : @Measure (AdelicGL2 (𝓞 F) F) mS
  D : Set (AdelicGL2 (𝓞 F) F)
  Z : Subgroup (AdeleRing (𝓞 F) F)ˣ
  U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)
  gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F
  nS : MeasurableSpace (AdeleRing (𝓞 F) F)
  ν : @Measure (AdeleRing (𝓞 F) F) nS

/-- The production carrier pins: Haar measures on the adelic group and the
normalized measure on the set `B` of adeles. -/
public def productionPinsOf (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    CarrierPins F where
  mS := glBorel (Fin 2) (𝓞 F) F
  μ := adelicGLHaar (Fin 2) (𝓞 F) F
  D := D
  Z := ⊤
  U := U
  gen := gen
  nS := adeleBorel (𝓞 F) F
  ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B

public theorem productionPinsOf_mS (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).mS = glBorel (Fin 2) (𝓞 F) F := rfl

public theorem productionPinsOf_μ (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

public theorem productionPinsOf_Z (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).Z = ⊤ := rfl

public theorem productionPinsOf_nS (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).nS = adeleBorel (𝓞 F) F := rfl

public theorem productionPinsOf_D (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).D = D := rfl

public theorem productionPinsOf_U (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).U = U := rfl

public theorem productionPinsOf_gen (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).gen = gen := rfl

public theorem productionPinsOf_ν (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    (productionPinsOf F D U gen B).ν
      = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B := rfl

public theorem isHaarMeasure_productionPinsOf_μ (F : Type*) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    @Measure.IsHaarMeasure _ _ _ (productionPinsOf F D U gen B).mS
      (productionPinsOf F D U gen B).μ :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

public theorem isProbabilityMeasure_productionPinsOf_ν (F : Type*) [Field F]
    [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (hB0 : adelicAddHaar (𝓞 F) F B ≠ 0) (hBtop : adelicAddHaar (𝓞 F) F B ≠ ⊤) :
    @IsProbabilityMeasure _ (productionPinsOf F D U gen B).nS
      (productionPinsOf F D U gen B).ν := by
  letI := adeleBorel (𝓞 F) F
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBtop

end AutomorphicForm

end
