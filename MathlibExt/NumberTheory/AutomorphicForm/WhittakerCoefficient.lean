/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean`
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

public import MathlibExt.NumberTheory.AutomorphicForm.CarrierPins
public import MathlibExt.NumberTheory.AutomorphicForm.ConstantTerm
public import MathlibExt.NumberTheory.NumberField.AdelicFourier
public import MathlibExt.NumberTheory.NumberField.GlobalAddChar

@[expose] public section

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type*) [Field F] [NumberField F]

/-- The `α`-th Whittaker coefficient of `φ` at `g`: the adelic Fourier integral of
`x ↦ φ (unipotentGL2 x * g)` against the pinned measure on the adeles, evaluated at `α`. -/
public def whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := pins.nS
  NumberField.AdelicFourier.fourierIntegral ψ pins.ν (fun x => φ (unipotentGL2 x * g))
    (algebraMap F (AdeleRing (𝓞 F) F) α)

/-- Integrability of the Whittaker-coefficient integrand, in the form that
`NumberField.AdelicFourier.fourierIntegral` integrates. -/
public def WhittakerCoefficientIntegrable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : Prop :=
  letI := pins.nS
  Integrable
    (fun x => ψ (-(x * algebraMap F (AdeleRing (𝓞 F) F) α)) * φ (unipotentGL2 x * g)) pins.ν

public theorem whittakerCoefficient_eq_integral (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α g =
      ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν := by
  letI := pins.nS
  simp only [whittakerCoefficient, NumberField.AdelicFourier.fourierIntegral]
  congr 1 with x
  rw [mul_comm x]
  exact mul_comm _ _

@[simp] public theorem whittakerCoefficient_zero (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 := by
  letI := pins.nS
  simp only [whittakerCoefficient, NumberField.AdelicFourier.fourierIntegral, mul_zero,
    integral_zero]

public theorem whittakerCoefficient_zero_eq_constantTerm (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g := by
  letI := pins.nS
  simp only [whittakerCoefficient, NumberField.AdelicFourier.fourierIntegral, map_zero,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  rfl

end AutomorphicForm

end
