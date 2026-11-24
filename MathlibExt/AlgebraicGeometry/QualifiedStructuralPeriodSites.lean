/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticBaseWittScalarSources
public import MathlibExt.AlgebraicGeometry.AnalyticCoefficientPeriodScalars

/-!
# Source-qualified native structural period sites

This is source integration data for ONE actual analytic space. Regular
and positive rings, their original scalar inclusion, the completed
untilt/Witt objects, structural pushout and both period localizations are
FIXED native constructions. The residue scalar is pinned to Gamma of the
actual base field and all finite Witt coordinates. Local theta-line
existence is a source proof. No higher bundle or comparison is present.

Source construction/proof endpoints are direct Wanted declarations,
so having completed providers is independent of interface coverage.

References: Scholze, arXiv:1205.3463v2, Definitions 6.1 and 6.8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
Native Mathlib: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.QualifiedStructuralPeriodSites

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open AnalyticProEtaleCoefficientSources AnalyticBaseWittScalarSources
open MathlibExt.CategoryTheory.WittStructuralScalarBindings
open MathlibExt.CategoryTheory.UntiltingSheafSources
open MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources
open MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  [IsIso (MathlibExt.CategoryTheory.NativeRingInverseImages.constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]

structure Source where
  locallyNoetherian : AnalyticProObjectSites.IsLocallyNoetherian p X.left
  regularSheaf : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (etaleRingsLarge p X.left)
  integral : IntegralStructure p X.left
  positiveSheaf : Presheaf.IsSheaf (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (integral.presheaf ⋙ liftRings)
  untilting : UntiltingData p (originalPositive p X.left P integral positiveSheaf)
  cohen : CohenWittSource p K
  cohenEtale : CohenEtaleSource p K B X integral positiveSheaf cohen
  residue : QualifiedResidueSource p K B X P integral positiveSheaf cohen cohenEtale
  regularLocalization : RegularLocalizationSource p (originalStructure p X.left P regularSheaf)
    (originalPositive p X.left P integral positiveSheaf)
      (AnalyticBaseWittScalarSources.positiveInclusion p K B X P integral positiveSheaf regularSheaf)
  scalarSquare : ResidueScalarSource.ScalarSquare (p := p) (K := K)
    (O := originalStructure p X.left P regularSheaf)
    (Rplus := originalPositive p X.left P integral positiveSheaf)
    (positiveInclusion := AnalyticBaseWittScalarSources.positiveInclusion
      p K B X P integral positiveSheaf regularSheaf)
    (S := residue.residue) regularLocalization untilting
  thetaLine : IsLocallyThetaLine untilting.deRhamPositive
    (completedRegular p (originalPositive p X.left P integral positiveSheaf)) untilting.completedTheta

namespace Source

variable (S : Source p K B X P)

def regular := originalStructure p X.left P S.regularSheaf
def positive := originalPositive p X.left P S.integral S.positiveSheaf

/-- The actual source scalar maps, from the original Cohen, Witt and completion units. -/
def scalars : WittScalarSource p K S.regular S.positive S.untilting :=
  ResidueScalarSource.structuralScalars (p := p) (K := K)
    (O := S.regular) (Rplus := S.positive)
    (positiveInclusion := AnalyticBaseWittScalarSources.positiveInclusion
      p K B X P S.integral S.positiveSheaf S.regularSheaf)
    (S := S.residue.residue) S.regularLocalization S.untilting S.scalarSquare

def absolutePositive := S.untilting.deRhamPositive
def absoluteFull := WittScalarSource.absoluteFull p S.positive S.untilting
def naiveStructuralPositive := S.scalars.naiveStructuralPositive
def naiveStructuralFull := S.scalars.naiveStructuralFull

end Source

end MathlibExt.AlgebraicGeometry.QualifiedStructuralPeriodSites
