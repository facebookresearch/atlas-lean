/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.HeckeEigensystem

@[expose] public section

open IsDedekindDomain NumberField

namespace AutomorphicFormHeckeEigensystemTest

/-- Consumer with the eigensystem and base-change binders: the formal base
change is a base change at every prime. -/
public theorem exactSource {F K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]
    (π : AutomorphicForm.HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsBaseChangeAt π
      (AutomorphicForm.formalBaseChange F K π) 𝔓 :=
  AutomorphicForm.formalBaseChange_isBaseChangeAt F K π 𝔓

/-- Higher-universe consumer. -/
public theorem exactSourceTypeOne {F K : Type 1} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type 1} [CommRing R]
    (π : AutomorphicForm.HeckeEigensystem F R) :
    AutomorphicForm.IsBaseChangeOf π
      (AutomorphicForm.formalBaseChange F K π) :=
  AutomorphicForm.formalBaseChange_isBaseChangeOf F K π

/-- At inertia degree one the eigenvalues are unchanged. -/
public example {F K : Type*} [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra (𝓞 F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]
    (π : AutomorphicForm.HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1) :
    (AutomorphicForm.formalBaseChange F K π).a 𝔓
      = π.a (𝔓.under (𝓞 F)) :=
  (AutomorphicForm.formalBaseChange_a_of_inertiaDeg_eq_one F K π 𝔓 h).1

/-- Twisting by the constant one function does not change `a`. -/
public example {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] (Φ : AutomorphicForm.HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) :
    (Φ.twist fun _ => 1).a v = Φ.a v := by
  rw [AutomorphicForm.HeckeEigensystem.twist_a, one_mul]

/-- The level hypothesis matters: the zero ideal is not a permitted level,
witnessed by the defining field `level_ne_bot`. -/
public example {F : Type*} [Field F] [NumberField F]
    {R : Type*} [CommRing R] (Φ : AutomorphicForm.HeckeEigensystem F R) :
    Φ.level ≠ ⊥ :=
  Φ.level_ne_bot

end AutomorphicFormHeckeEigensystemTest
