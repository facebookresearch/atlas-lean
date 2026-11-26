/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexesConstructibleScalarExtension

/-!
# Tests for scalar extension of bounded constructible complexes

Bounded constructibility is preserved by successive extensions from rational
to real to complex coefficients. Extension to complex coefficients also gives
cohomology vanishing outside a bounded range.

Sources: A. Dimca, *Sheaves in Topology*, Chapters 2–4; M. de Cataldo and
L. Migliorini, *The decomposition theorem, perverse sheaves and the topology
of algebraic maps*, arXiv:0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesConstructibleScalarExtension

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

attribute [local instance] HasDerivedCategory.standard

example (X : ComplexScheme) [IsComplexVariety X]
    (K : CoefficientDerived ℚ (space X)) (hK : boundedConstructible ℚ X K) :
    boundedConstructible ℂ X
      ((derivedScalarExtension ℝ ℂ (space X)).obj
        ((derivedScalarExtension ℚ ℝ (space X)).obj K)) :=
  constructible_scalarExtension ℝ ℂ X _ (constructible_scalarExtension ℚ ℝ X K hK)

example (X : ComplexScheme) [IsComplexVariety X]
    (K : CoefficientDerived ℚ (space X)) (hK : boundedConstructible ℚ X K) :
    ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((derivedScalarExtension ℚ ℂ (space X)).obj K)) :=
  (constructible_scalarExtension ℚ ℂ X K hK).1

end MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesConstructibleScalarExtension
