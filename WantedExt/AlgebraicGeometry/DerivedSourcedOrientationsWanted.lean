/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
public import Batteries.Util.ProofWanted

/-!
# Fully sourced orientation-family construction requests

The all-A family is chosen jointly with its complete enriched source
realizations. Compactness, scalar base-change and perfection of actual
RΓ are separate source proofs. Duality uses closed representatives and
explicit native triangle homotopies.
Reference: PTVV arXiv:1111.3209v4, Definitions 2.1–2.4.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedScalarGlobalSections
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedOrientationModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u

def_wanted compatibleSourcedFamily (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : DerivedStack Q) : SourcedFamilyModel M U R Q L V X.functor

def_wanted compatibleSourcedScalarFamily (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : DerivedStack Q) : SourcedScalarFamily M U R Q L V X.functor

theorem_wanted actualStructureUnitPerfect (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : FamilyModel M U Q L V X) :
    ∀ A : SAlg k, IsPerfect (B.model A) (B.model A).unit

theorem_wanted actualCompactScalarBaseChange (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : SourcedScalarFamily M U R Q L V X)
    (compact : IsSourcedOCompact B.family) : IsScalarBaseChange B.family.model B.absolute B.scalar

theorem_wanted actualCompactGammaPerfect (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : SourcedScalarFamily M U R Q L V X)
    (compact : IsSourcedOCompact B.family) :
    IsPerfectModule (scalarCategory (LargeScalar k)) B.scalar.source.module

def_wanted actualPerfectHomotopyDual (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M) (R : RawModuleRealization M)
    (L : CochainLiftModel k) (X : Prestack k) (G : QCohEnhancement M U X)
    (C : GammaCechData L G)
    (source : SourcedCoefficientImageModel C.category R G C.source C.unit)
    (H : CoherentMonoidalEnhancement G) (E : G.category) (perfect : IsPerfect G E) :
    PerfectDual H.monoidal E

theorem_wanted nativeCoefficientPairingBalanced (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (X : Prestack k) (B : FamilyModel M U Q L V X) (G : QCohEnhancement M U X)
    (H : OrientationContext B G) (A : SAlg k) (E : (B.model A).category)
    (P : PerfectDual (H.family A).monoidal E)
    (R₁ : ModuleReplacement (gamma B A E)) (R₂ : ModuleReplacement (gamma B A P.object)) :
    IsBalancedCoefficientPairing B G H A P R₁ R₂

end MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations
