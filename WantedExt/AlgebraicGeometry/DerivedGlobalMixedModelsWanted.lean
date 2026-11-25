/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
public import Batteries.Util.ProofWanted

/-!
# Actual global mixed/NC model construction requests

Every output retains its full affine-family diagram, actual coefficient
lift, mixed epsilon and all NC closing coefficients. Comparison
quasi-isomorphisms are separate proofs of the computed maps.
References: PTVV arXiv:1111.3209v4, §1.1 and §2.1; Bousfield–Kan.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels

open _root_.CategoryTheory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedMixedLocalizationModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalNCIntegration
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry

universe u

def_wanted nativeMixedCoefficientLift (k : Type u) [CommRing k]
    (L : CochainLiftModel k) : MixedLiftModel L

def_wanted nativeGlobalMixedLimit (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (X : Prestack k) : GlobalMixedModel D T X

def_wanted nativeLiftedNC (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) : LiftedNCDiagram D T p N

def_wanted nativeReplacementNC (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k)
    (G : GlobalMixedModel D T X) (A : LiftedNCDiagram D T p N) : ReplacementNCDiagram G A

def_wanted nativeMixedLimitNC (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k)
    (G : GlobalMixedModel D T X) (A : LiftedNCDiagram D T p N)
    (I : ReplacementNCDiagram G A) : MixedLimitNC I

def_wanted nativeGlobalNCAugmentationLift (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k)
    (G : GlobalMixedModel D T X) (A : LiftedNCDiagram D T p N)
    (I : ReplacementNCDiagram G A) (F : GlobalNCModel D p N X) : GlobalNCLift I F

def_wanted nativeGlobalNCPacket (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k)
    (G : GlobalMixedModel D T X) (F : GlobalNCModel D p N X) : GlobalNCData G F

theorem_wanted nativeGlobalNCComparisonQuasiIso (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (p : ℕ)
    (N : NegativeCyclicDiagram D.functor (p : ℤ)) (X : Prestack k)
    (G : GlobalMixedModel D T X) (F : GlobalNCModel D p N X) (A : GlobalNCData G F)
    (C : NCCategoryModel (LargeScalar k) (p : ℤ)) : QuasiIso (A.comparison C)

def_wanted nativeMixedPullback (k : Type u) [CommRing k]
    (Q : AlgebraReplacementFunctor k) (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (T : MixedLiftModel L) (X Y : Prestack k) (f : X ⟶ Y)
    (GY : GlobalMixedModel D T Y) (GX : GlobalMixedModel D T X) : MixedPullbackModel f GY GX

def_wanted nativeWeightedNCFunctor (R : Type u) [CommRing R] (p : ℤ) : NCCategoryModel R p

end MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
