/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.IntersectionComplexes
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

@[expose] public section

/-!
# Tests for intermediate extensions and intersection complexes

`L[d]` is `L` placed in cohomological degree `-d`, so its cohomology in degree
`-d` is `L`. Restriction is the derived exact inverse image. Every
intermediate extension is faithful, and the intersection complex of a local
system on a smooth open restricts to `L[d]` through the two given comparisons;
constant sheaves of finite-dimensional spaces qualify.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.IntersectionComplexes

namespace MathlibExtTest.AlgebraicGeometry.IntersectionComplexes

attribute [local instance] HasDerivedCategory.standard

/-- The cohomology of `L[d]` in degree `-d` is `L`. -/
example (U : PerverseSheaves.ComplexScheme) (L : RationalSheaf (space U)) (d : ℕ) :
    (DerivedCategory.homologyFunctor _ (-(d : ℤ))).obj (normalizedLocalSystem U L d) ≅ L :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-(d : ℤ))).app L

/-- Restriction is the derived exact inverse image along the complex points. -/
example {U X : PerverseSheaves.ComplexScheme} (j : U ⟶ X) :
    derivedRestriction j = ConstructibleComplexes.derivedPullback ℚ (spaceMap j) :=
  rfl

variable {U X : PerverseSheaves.ComplexScheme} [IsComplexVariety U] [IsComplexVariety X]
  [PerverseSheafTheory U] [PerverseSheafTheory X] (j : U ⟶ X)

/-- Every intermediate extension is faithful. -/
example (J : IntermediateExtensionData j) : J.functor.Faithful := inferInstance

/-- Boundary support is vanishing of the restriction. -/
example (P : PerverseSheaf X) :
    IsBoundarySupported j P ↔ IsZero ((derivedRestriction j).obj ((perverseAmbient X).obj P)) :=
  Iff.rfl

/-- The intersection complex of a local system on a smooth open restricts to
`L[d]` through the restriction isomorphism of the intermediate extension and the
realization of `L[d]`. -/
example [IsOpenImmersion j.left] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) [SmoothOfRelativeDimension d U.hom]
    (hL : IsFiniteRankLocalSystem (space U) L) (R : LocalSystemPerverseRealization U L d) :
    (intersectionComplex_restriction j J L d hL R).hom =
      (J.restriction.app R.object).hom ≫ R.comparison.hom :=
  rfl

example [IsOpenImmersion j.left] (J : IntermediateExtensionData j)
    (L : RationalSheaf (space U)) (d : ℕ) [SmoothOfRelativeDimension d U.hom]
    (hL : IsFiniteRankLocalSystem (space U) L) (R : LocalSystemPerverseRealization U L d) :
    intersectionComplex j J L d hL R = J.functor.obj R.object :=
  rfl

/-- The constant sheaf of a finite-dimensional space is a local system, so it
has an intersection complex. -/
example [IsOpenImmersion j.left] (J : IntermediateExtensionData j) (d : ℕ)
    [SmoothOfRelativeDimension d U.hom]
    (R : LocalSystemPerverseRealization U (rationalConstantSheaf (space U)) d) :
    PerverseSheaf X :=
  intersectionComplex j J _ d
    (ConstructibleComplexes.isFiniteRankLocalSystem_constantSheaf ℚ _ (ModuleCat.of ℚ ℚ)) R

end MathlibExtTest.AlgebraicGeometry.IntersectionComplexes
