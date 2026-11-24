/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.FiniteAlgebraDecomposition

/-- The original `Type` statement, with its original binders, follows from
the universe-polymorphic theorem. -/
example {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) :=
  Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite A

/-- Higher-universe consumer: the theorem also applies in `Type 1`. -/
example {𝒪 : Type 1} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type 1) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) :=
  Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite A

/-- In particular, taking the algebra to be the base ring itself gives the
bijective decomposition for the base. -/
example {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] :
    Finite (MaximalSpectrum 𝒪) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum 𝒪 =>
        algebraMap 𝒪 (Localization.AtPrime I.asIdeal)) :=
  ⟨(Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
      (𝒪 := 𝒪) 𝒪).1,
    (Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
      (𝒪 := 𝒪) 𝒪).2.1⟩
