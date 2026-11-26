/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.OpenFlatLocus

@[expose] public section

/-- The theorem restated with its original binders. -/
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} :=
  Module.Flat.isOpen_setOf_flat_localization_atPrime

/-- A consumer at a fixed higher universe. -/
example {A B : Type 1} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Algebra.FiniteType A B] :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} :=
  Module.Flat.isOpen_setOf_flat_localization_atPrime

/-- A concrete instance: a field over itself. -/
example {K : Type*} [Field K] :
    IsOpen {Q : PrimeSpectrum K | Module.Flat K (Localization.AtPrime Q.asIdeal)} :=
  Module.Flat.isOpen_setOf_flat_localization_atPrime

/-- A concrete instance: the polynomial ring `ℤ[X]` over `ℤ`. -/
example := Module.Flat.isOpen_setOf_flat_localization_atPrime (A := ℤ) (B := Polynomial ℤ)
