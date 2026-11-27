/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.GenericFlatness

import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

open TensorProduct

example {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) :=
  Module.Flat.exists_ne_zero_flat_localization_tensorProduct

universe u v w in
example {A : Type u} {B : Type v} {M : Type w} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) :=
  Module.Flat.exists_ne_zero_flat_localization_tensorProduct (A := A) (B := B) (M := M)

/-- A concrete instance: `ℤ[X]` as a module over itself, over the Noetherian domain `ℤ`. -/
example :=
  Module.Flat.exists_ne_zero_flat_localization_tensorProduct (A := ℤ) (B := Polynomial ℤ)
    (M := Polynomial ℤ)
