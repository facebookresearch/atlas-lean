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

/-!
# Closure, preservation and coefficients for constructible complexes

The requests use actual sheaves, kernels/cokernels, algebraic stratifications
and derived functors. No perverse-theory or decomposition request is included.
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

/-- Field extension, followed by sheafification, is exact. -/
public instance_wanted scalarExtension_exact (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) : ScalarExtensionExact k l Z

/-- Kernels of morphisms of finite-rank local systems are finite-rank local systems. -/
public theorem_wanted localSystem_kernel (k : Type) [Field k] (Z : TopCat.{0})
    (F G : CoefficientSheaf k Z) (a : F ⟶ G)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F)
    (hG : ConstructibleComplexes.IsFiniteRankLocalSystem k Z G) :
    ConstructibleComplexes.IsFiniteRankLocalSystem k Z (kernel a)

/-- Cokernels of such morphisms remain finite-rank local systems. -/
public theorem_wanted localSystem_cokernel (k : Type) [Field k] (Z : TopCat.{0})
    (F G : CoefficientSheaf k Z) (a : F ⟶ G)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F)
    (hG : ConstructibleComplexes.IsFiniteRankLocalSystem k Z G) :
    ConstructibleComplexes.IsFiniteRankLocalSystem k Z (cokernel a)

/-- Field extension preserves local triviality and finite rank. -/
public theorem_wanted scalarExtension_localSystem (k l : Type) [Field k] [Field l]
    [Algebra k l] (Z : TopCat.{0}) (F : CoefficientSheaf k Z)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F) :
    ConstructibleComplexes.IsFiniteRankLocalSystem l Z ((scalarExtension k l Z).obj F)

/-- Bounded algebraically constructible complexes form a triangulated subcategory. -/
public instance_wanted constructible_isTriangulated (k : Type) [Field k]
    (X : ComplexScheme) [IsComplexVariety X] :
    (ConstructibleComplexes.boundedConstructible k X).IsTriangulated

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
