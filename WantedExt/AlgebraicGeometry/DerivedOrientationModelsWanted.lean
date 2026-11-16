/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedOrientationModels
public import Batteries.Util.ProofWanted

/-!
# Actual scalar traces and orientation adjunction construction requests

The source trace is RΓ(X,O_X)→k[-d]. Its A-linear extension, actual
cup/dual evaluation, replacement augmentations and coefficient-linear
transpose are all fixed by the public contracts. Nondegeneracy remains
the source orientation criterion; no generic producer supplies it.

Reference: PTVV arXiv:1111.3209v4, §2.1, Definitions 2.1--2.4.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DerivedOrientationModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open CochainComplex.HomComplex

universe u v

def_wanted nativeScalarUnitSelector (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] (o : C) : UnitFunctorModel (R := R) C o

def_wanted nativeScalarUnitEvaluation (R : Type u) [CommRing R]
    (C : Cochains R) : UnitEvaluationModel C

def_wanted sourceScalarGlobalModels (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) :
    (B : FamilyModel M U Q L V X) × (G : QCohEnhancement M U X) × ScalarGlobalModels B G

def_wanted actualScalarTraceSystem (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : FamilyModel M U Q L V X) (compact : IsOCompact B)
    (G : QCohEnhancement M U X) (D : ScalarGlobalModels B G)
    (baseChange : IsScalarBaseChange B G D) (d : ℤ)
    (η : Cocycle (globalHom G G.unit) (𝟙_ (Cochains (LargeScalar k))) (-d)) :
    {T : TraceSystem B G D d // T.absolute = η}

def_wanted actualCoefficientDualPairing (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : FamilyModel M U Q L V X) (G : QCohEnhancement M U X)
    (D : ScalarGlobalModels B G) (C : OrientationContext B G)
    (A : SAlg k) (E : (B.model A).category) (perfect : IsPerfect (B.model A) E)
    (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S' : ModuleReplacement (gamma B A P.object))
    (balanced : IsBalancedCoefficientPairing B G C A P R S') :
    CoefficientPairingModel B G D C A P R S'

def_wanted actualOrientationAdjoint (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : FamilyModel M U Q L V X) (G : QCohEnhancement M U X)
    (D : ScalarGlobalModels B G) (d : ℤ) (T : TraceSystem B G D d)
    (C : OrientationContext B G) (A : SAlg k) (E : (B.model A).category)
    (P : PerfectDual (C.family A).monoidal E)
    (R : ModuleReplacement (gamma B A E)) (S' : ModuleReplacement (gamma B A P.object))
    (K : CoefficientPairingModel B G D C A P R S') : OrientationAdjointModel B G D T C A P R S' K

end MathlibExt.AlgebraicGeometry.DerivedOrientationModels
