/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel

/-!
# Closure, preservation and coefficients for constructible complexes

The requests use actual sheaves, kernels, algebraic stratifications
and derived functors; the cokernel statement for local systems
(`localSystem_cokernel`) is proved in
`MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel`,
and the kernel statement for local systems (`localSystem_kernel`) is proved in
`MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel`.
The perverse t-structure is not requested here.
Sources: Dimca, *Sheaves in Topology*, Chapters 2–4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

/-- Field extension preserves local triviality and finite rank. -/
public theorem_wanted scalarExtension_localSystem (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) (F : CoefficientSheaf k Z)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F) :
    ConstructibleComplexes.IsFiniteRankLocalSystem l Z ((scalarExtension k l Z).obj F)

/-- Bounded algebraically constructible complexes form a triangulated subcategory. -/
public instance_wanted constructible_isTriangulated (k : Type) [Field k]
    (X : ComplexScheme) [IsComplexVariety X] :
    (ConstructibleComplexes.boundedConstructible k X).IsTriangulated

/-- The constant sheaf of a complex variety, placed in any single degree, is
bounded constructible: a complex variety has a finite partition into smooth
locally closed subvarieties, on which the constant sheaf restricts to a
constant sheaf. -/
public theorem_wanted constructible_constantSheaf (k : Type) [Field k]
    (X : ComplexScheme) [IsComplexVariety X] (n : ℤ) :
    ConstructibleComplexes.boundedConstructible k X
      (DerivedCategory.Plus.ι.obj
        ((DerivedCategory.Plus.singleFunctor (CoefficientSheaf k (space X)) n).obj
          ((constantSheaf (Opens.grothendieckTopology (space X)) (ModuleCat.{0} k)).obj
            (ModuleCat.of k k))))

/-- Algebraic inverse image preserves bounded constructibility. -/
public theorem_wanted constructible_pullback (k : Type) [Field k]
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y] (f : X ⟶ Y)
    (K : CoefficientDerived k (space Y))
    (hK : ConstructibleComplexes.boundedConstructible k Y K) :
    ConstructibleComplexes.boundedConstructible k X
      ((derivedPullback k (spaceMap f)).obj K)

/-- Proper algebraic direct image preserves bounded constructibility. -/
public theorem_wanted constructible_proper_pushforward (k : Type) [Field k]
    (X Y : ComplexScheme) [IsComplexVariety X] [IsComplexVariety Y] (f : X ⟶ Y)
    [IsProper f.left] (K : DerivedCategory.Plus (CoefficientSheaf k (space X)))
    (hK : ConstructibleComplexes.boundedConstructible k X
      (DerivedCategory.Plus.ι.obj K)) :
    ConstructibleComplexes.boundedConstructible k Y ((derivedPushforwardPlus k f).obj K)

/-- Derived field extension preserves the same algebraic stratification property. -/
public theorem_wanted constructible_scalarExtension (k l : Type) [Field k] [Field l]
    [Algebra k l] (X : ComplexScheme) [IsComplexVariety X]
    (K : CoefficientDerived k (space X))
    (hK : ConstructibleComplexes.boundedConstructible k X K) :
    ConstructibleComplexes.boundedConstructible l X
      ((derivedScalarExtension k l (space X)).obj K)

end WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted
