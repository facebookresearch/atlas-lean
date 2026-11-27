/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AutomorphicForm_HeckeEigensystem.lean` and
`Definitions/Def_AutomorphicForm_FormalBaseChange.lean`
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

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import MathlibExt.NumberTheory.AutomorphicForm.SatakePow

@[expose] public section

open IsDedekindDomain NumberField

namespace AutomorphicForm

/-- A Hecke eigensystem over a number field: a nonzero level together with
the two eigenvalue functions `a` and `b` at height-one primes. -/
public structure HeckeEigensystem (F : Type*) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where
  /-- The level ideal. -/
  level : Ideal (𝓞 F)
  /-- The level is nonzero. -/
  level_ne_bot : level ≠ ⊥
  /-- The first eigenvalue function. -/
  a : HeightOneSpectrum (𝓞 F) → R
  /-- The second eigenvalue function. -/
  b : HeightOneSpectrum (𝓞 F) → R

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]

/-- Twisting an eigensystem by a scalar function scales `a` by the function
and `b` by its square, keeping the same level. -/
public def twist (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) : HeckeEigensystem F R where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => χ v * Φ.a v
  b := fun v => χ v ^ 2 * Φ.b v

@[simp]
public theorem twist_a (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) (v : HeightOneSpectrum (𝓞 F)) :
    (Φ.twist χ).a v = χ v * Φ.a v :=
  rfl

@[simp]
public theorem twist_b (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) (v : HeightOneSpectrum (𝓞 F)) :
    (Φ.twist χ).b v = χ v ^ 2 * Φ.b v :=
  rfl

/-- Two eigensystems agree away from a finite set of primes when their
eigenvalue functions coincide outside that set. -/
public def AgreesAwayFromFinite (Φ Φ' : HeckeEigensystem F R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
    ∀ v ∉ S, Φ.a v = Φ'.a v ∧ Φ.b v = Φ'.b v

/-- An eigensystem is constant on fibres over a smaller field when, outside
a finite set, primes with the same underlying prime and the same inertia
degree have the same eigenvalues. -/
public def IsConstantOnFibers {L : Type*} [Field L] [NumberField L]
    (Φ : HeckeEigensystem L R) (E : Type*) [Field E] [NumberField E]
    [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)] : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)),
    ∀ 𝔓₁ ∉ S, ∀ 𝔓₂ ∉ S,
      𝔓₁.under (𝓞 E) = 𝔓₂.under (𝓞 E) →
      (𝔓₁.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₁.asIdeal
        = (𝔓₂.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Φ.a 𝔓₁ = Φ.a 𝔓₂ ∧ Φ.b 𝔓₁ = Φ.b 𝔓₂

end HeckeEigensystem

section Transfer

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]
  {R : Type*} [CommRing R]

/-- An eigensystem over `L` is the base change of one over `E` at a prime
when its eigenvalues there are the Satake power and the power of the
eigenvalues at the underlying prime, with exponent the inertia degree. -/
public def IsBaseChangeAt (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) (𝔓 : HeightOneSpectrum (𝓞 L)) : Prop :=
  Φ.a 𝔓 = satakePow ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)
            (π.a (𝔓.under (𝓞 E))) (π.b (𝔓.under (𝓞 E))) ∧
  Φ.b 𝔓 = (π.b (𝔓.under (𝓞 E)))
    ^ ((𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal)

/-- An eigensystem over `L` is a base change of one over `E` when it is a
base change at every prime outside a finite set. -/
public def IsBaseChangeOf (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ 𝔓 ∉ S, IsBaseChangeAt π Φ 𝔓

/-- Descent is base change read in the opposite direction. -/
public def IsDescentOf (Φ : HeckeEigensystem L R)
    (π : HeckeEigensystem E R) : Prop :=
  IsBaseChangeOf π Φ

end Transfer

section FormalBaseChange

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

/-- The formal base change of an eigensystem: at each prime of `K`, the
eigenvalues are the Satake power and the power determined by the prime
below and its inertia degree. The level is the unit ideal. -/
public noncomputable def formalBaseChange (π : HeckeEigensystem F R) :
    HeckeEigensystem K R where
  level := ⊤
  level_ne_bot := by simp
  a := fun 𝔓 => satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
    (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F)))
  b := fun 𝔓 => (π.b (𝔓.under (𝓞 F)))
    ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

@[simp]
public theorem formalBaseChange_a (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).a 𝔓 =
      satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
        (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F))) :=
  rfl

@[simp]
public theorem formalBaseChange_b (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).b 𝔓 =
      (π.b (𝔓.under (𝓞 F)))
        ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) :=
  rfl

/-- The formal base change has the unit level. -/
public theorem formalBaseChange_level (π : HeckeEigensystem F R) :
    (formalBaseChange F K π).level = ⊤ :=
  rfl

/-- The formal base change is a base change at every prime. -/
public theorem formalBaseChange_isBaseChangeAt (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    IsBaseChangeAt π (formalBaseChange F K π) 𝔓 :=
  ⟨rfl, rfl⟩

/-- The formal base change is a base change with empty exceptional set. -/
public theorem formalBaseChange_isBaseChangeOf (π : HeckeEigensystem F R) :
    IsBaseChangeOf π (formalBaseChange F K π) :=
  ⟨∅, fun 𝔓 _ => formalBaseChange_isBaseChangeAt F K π 𝔓⟩

/-- At a prime of inertia degree one, the formal base change recovers the
eigenvalues at the prime below. -/
public theorem formalBaseChange_a_of_inertiaDeg_eq_one
    (π : HeckeEigensystem F R) (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1) :
    (formalBaseChange F K π).a 𝔓 = π.a (𝔓.under (𝓞 F)) ∧
      (formalBaseChange F K π).b 𝔓 = π.b (𝔓.under (𝓞 F)) := by
  constructor <;> simp only [formalBaseChange_a, formalBaseChange_b, h, satakePow_one, pow_one]

end FormalBaseChange

end AutomorphicForm
