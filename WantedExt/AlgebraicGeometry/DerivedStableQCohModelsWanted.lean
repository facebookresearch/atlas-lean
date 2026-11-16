/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedStableQCohModels
public import Batteries.Util.ProofWanted

/-!
# Wanted source-compatible stable QCoh enhancements and native fibres

The QCoh factory chooses an enhancement together with its full DG
Yoneda shift/cone realization. This records source stability before
positive-degree Hom comparisons are requested. Relative fibres and
exterior images are normalized to the native module cone and skew
projector, independently of symplectic nondegeneracy.

References: Keller, Deriving DG categories, §2; PTVV1111.3209v4 §§1.2/2.2.
-/

open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels
open MathlibExt.AlgebraicGeometry.DerivedStableQCohModels

universe u

def_wanted source_stable_qcoh_enhancement (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (X : Prestack k) :
    Σ G : QCohEnhancement M U X, StableQCohModel G

def_wanted native_relative_tangent_fibre (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) (G : QCohEnhancement M U X) (P : StableQCohModel G)
    (T V : G.category) (a : DGHom (LargeScalar k) 0 T V)
    (ha : a ∈ dgCycles (LargeScalar k) T V) : RelativeTangent a ha

def_wanted native_derived_exterior_square (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) (G : QCohEnhancement M U X) (P : StableQCohModel G)
    (H : CoherentMonoidalEnhancement G) (L : G.category) : ExteriorSquare H L

def_wanted native_derived_perfect_dual (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (X : Prestack k) (G : QCohEnhancement M U X) (P : StableQCohModel G)
    (H : CoherentMonoidalEnhancement G) (E : G.category) (perfect : IsPerfect G E) :
    PerfectDual H.monoidal E
