/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.IntegrallyClosed.FaithfullyFlat
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public section

universe u v

/-- Consumer with the original binders. -/
example (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_faithfullyFlat (A := A) (B := B)

/-- Higher-universe consumer. -/
example (A : Type (u + 1)) (B : Type (v + 1)) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.FaithfullyFlat A B]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_faithfullyFlat (A := A) (B := B)

/-- Concrete consumer: the identity algebra on `ℤ`. -/
example : IsIntegrallyClosed ℤ :=
  IsIntegrallyClosed.of_faithfullyFlat (A := ℤ) (B := ℤ)
