/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Finiteness.FiniteTypeOfFaithfullyFlat

@[expose] public section

universe u v w

example (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B] [Algebra.FiniteType R B] :
    Algebra.FiniteType R A :=
  Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation R A B

example : Algebra.FiniteType ℤ ℤ :=
  Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation ℤ ℤ ℤ

-- A concrete instance: `ℤ → ℤ[X] → ℤ[X][Y]`, where `ℤ[X][Y]` is free, hence faithfully flat,
-- and finitely presented over `ℤ[X]`.
example : Algebra.FiniteType ℤ (Polynomial ℤ) :=
  Algebra.FiniteType.of_faithfullyFlat_of_finitePresentation ℤ (Polynomial ℤ)
    (Polynomial (Polynomial ℤ))
