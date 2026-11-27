/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantDerivedObstructionModels

/-!
# The fixed source and its actual induced derived obstruction morphism

The source terms are the original weight-zero bundle summands and their
computed restricted differential. The source comparison uses those
actual inclusions in both nonzero degrees. The fixed morphism is the
native derived restriction of the original phi followed by the actual
cotangent square map. Homology conditions for this exact morphism are
separate theorem goals, not a fixed-POT assignment.

Source: Graber--Pandharipande alg-geom/9708001v2, Section1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FixedDerivedObstructionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonObj
open GlobalObstructionMorphisms GlobalPerfectObstructionTheory GlobalPOTVirtualClass
open TorusFixedSchemeModels AlgebraicWeightBundleModels DerivedTwoTermObstructionModels
open SchemeDerivedCotangentPullbacks CotangentSquareResolutionMaps GlobalCotangentSquareMaps
open EquivariantDerivedObstructionModels
attribute [local instance] HasDerivedCategory.standard

variable {X F : Over base} [ModObj Gm X] (E : EquivariantObstructionTerms X)
  (i : F ⟶ X) (hi : FixedPoint Gm X i) (W : FixedTerms E i hi)

/-- The constant rank is the sum over the actual character-zero summands. -/
def fixedRank {L : X.left.Modules} {A : LinearizedLineBundles.Linearization Gm X L}
    (D : WeightDecomposition A i hi) : ℕ := by
  classical
  exact ∑ j : Fin D.count, if IsTrivialCharacter (D.character j) then D.rank j else 0

/-- These are bundle proofs for the actual native weight-zero biproducts. -/
structure FixedBundleData where
  negative : AlgebraicBundleGeometry.IsBundle W.negative.fixed (fixedRank i hi W.negative)
  degreeZero : AlgebraicBundleGeometry.IsBundle W.degreeZero.fixed (fixedRank i hi W.degreeZero)

def fixedModel (B : FixedBundleData E i hi W) : TwoTermModel F.left where
  negative := W.negative.fixed
  degreeZero := W.degreeZero.fixed
  negativeRank := fixedRank i hi W.negative
  zeroRank := fixedRank i hi W.degreeZero
  negative_bundle := B.negative
  zero_bundle := B.degreeZero
  differential := W.fixedDifferential

/-- The inclusion in the native pulled source is fixed by the actual summand maps. -/
structure FixedSourceData (B : FixedBundleData E i hi W) where
  map : sourceComplex (fixedModel E i hi W B) ⟶
    ((Scheme.Modules.pullback i.left).mapHomologicalComplex (.up ℤ)).obj
      (sourceComplex E.obstruction.model)
  zero : sourceZeroInclusion (fixedModel E i hi W B) ≫ map.f 0 =
    W.degreeZero.fixedInclusion ≫ (Scheme.Modules.pullback i.left).map
      (sourceZeroInclusion E.obstruction.model)
  negative : sourceNegativeInclusion (fixedModel E i hi W B) ≫ map.f (-1) =
    W.negative.fixedInclusion ≫ (Scheme.Modules.pullback i.left).map
      (sourceNegativeInclusion E.obstruction.model)

/-- The actual closed-embedding cotangent square is retained before restricting phi. -/
def fixedSquare : SchemeSquare X.hom F.hom where
  top := i.left
  bottom := 𝟙 base
  commutes := by simpa only [Category.comp_id] using Over.w i

/-- All target and source maps refer to the original objects and native derived functor. -/
structure FixedObstructionData (B : FixedBundleData E i hi W) where
  source : FixedSourceData E i hi W B
  pullback : DerivedPullbackSource i.left
  acyclic : SourceAcyclic i.left pullback E.obstruction.model
  cotangent : CotangentNormalization F.hom
  differential : SquareMap (fixedSquare i) E.obstruction.cotangent cotangent

/-- The fixed phi is the actual composed restriction of the original derived morphism. -/
def FixedObstructionData.map {B : FixedBundleData E i hi W}
    (P : FixedObstructionData E i hi W B) :
    DerivedCategory.Q.obj (sourceComplex (fixedModel E i hi W B)) ⟶
      DerivedCategory.Q.obj P.cotangent.complex :=
  DerivedCategory.Q.map P.source.map ≫
    (sourceComparison i.left P.pullback E.obstruction.model P.acyclic).inv ≫
    (derivedPullback i.left P.pullback).map E.obstruction.map ≫ P.differential.derived P.pullback

/-- The POT homology conditions are conclusions about that particular native induced map. -/
def FixedPOTProperties {B : FixedBundleData E i hi W}
    (P : FixedObstructionData E i hi W B) : Prop :=
  IsIso ((DerivedCategory.homologyFunctor F.left.Modules 0).map P.map) ∧
    Epi ((DerivedCategory.homologyFunctor F.left.Modules (-1)).map P.map)

end MathlibExt.AlgebraicGeometry.FixedDerivedObstructionMaps
