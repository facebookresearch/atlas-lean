/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
public import MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
public import Batteries.Util.ProofWanted

/-!
# Full source Cech construction and comparison requests

The global enhancement is chosen jointly with its complete enriched
coefficient realization and Cech packet. Neither positive DG Hom nor
the whole categorical realization is inferred from a bare nerve model.
The actual coefficient-unit cone and all homogeneous Γ maps remain
fixed by the public source contracts.

References: PTVV arXiv:1111.3209v4, Definition 2.1 and pp.30–31;
HAG II math/0404373v7, §§1.3.7 and 1.4.1; enriched Yoneda.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u v w

def_wanted nativeFamilyCoefficientCategory (k : Type u) [CommRing k]
    (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k) (X : Prestack k) :
    FamilyCoefficientCategory L N X

def_wanted nativeRegularCoefficientSection (k : Type u) [CommRing k]
    (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k) (X : Prestack k)
    (C : FamilyCoefficientCategory L N X) : RegularCoefficientSection C

def_wanted nativeInjectiveCoefficientDiagram (R : Type u) [CommRing R]
    (J : Type v) [Category.{w} J] (D : J ⥤ Cochains R) : InjectiveDiagramReplacement D

def_wanted compatibleFullGammaCech (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (R : RawModuleRealization M) (Q : AlgebraReplacementFunctor k)
    (L : CochainLiftModel k) (X : DerivedStack Q) :
    (G : QCohEnhancement M U X.functor) × (C : GammaCechData L G) ×
      SourcedCoefficientImageModel C.category R G C.source C.unit

def_wanted actualCoefficientUnitLift (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (L : CochainLiftModel k) (X : Prestack k) (C : FamilyCoefficientCategory L N X)
    (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G)
    (B : EnrichedDiagramReplacement C G D) (V : UnitCoefficientDiagram C G D) :
    UnitCoefficientLift C G B V

def_wanted actualCoherentCoefficientUnit (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (L : CochainLiftModel k) (X : Prestack k) (C : FamilyCoefficientCategory L N X)
    (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G)
    (B : EnrichedDiagramReplacement C G D) (V : UnitCoefficientDiagram C G D)
    (T : UnitCoefficientLift C G B V) : CoherentUnitCone C G T

theorem_wanted actualAllEGammaComparisonQuasiIso (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (L : CochainLiftModel k) (X : Prestack k) (R : RawModuleRealization M)
    (G : QCohEnhancement M U X) (C : GammaCechData L G)
    (source : SourcedCoefficientImageModel C.category R G C.source C.unit) :
    ∀ E : G.category, QuasiIso (globalSectionMap C.category G C.comparison E)

end MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
