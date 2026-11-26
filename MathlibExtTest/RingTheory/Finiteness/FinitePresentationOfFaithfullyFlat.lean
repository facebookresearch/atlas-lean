/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Finiteness.FinitePresentationOfFaithfullyFlat

@[expose] public section

universe u v w

-- Consumer with the original binders: finite presentation descends along a faithfully
-- flat, finitely presented extension.
example (R : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A :=
  Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation R A B

-- The same consumer with all three rings in one universe, over the base `ℤ`.
example (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation ℤ B] :
    Algebra.FinitePresentation ℤ A :=
  Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation ℤ A B

-- A concrete instance: `ℤ → ℤ[X] → ℤ[X][Y]`, where `ℤ[X][Y]` is free, hence faithfully flat,
-- and finitely presented over `ℤ[X]`.
example : Algebra.FinitePresentation ℤ (Polynomial ℤ) :=
  Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation ℤ (Polynomial ℤ)
    (Polynomial (Polynomial ℤ))
