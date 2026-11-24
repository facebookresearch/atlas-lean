/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProEtaleDeRhamSources
public import MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation

/-!
# Native relative period comparison on the actual original/pro sources

The original complex is the native cochain inverse image of the
original affinoid-normalized etale relative de Rham complex. Its period
complex has the actual degreewise O_X tensor extension and total relative
connection over the pulled-back Y period ring. The maps below are the
native scalar projection followed by the native derived-adjunction mate
of the ORIGINAL cochain unit. IsIso is a Wanted conclusion, not input.

Reference: Scholze, arXiv:1205.3463v2, Proposition 8.5 and Theorem 8.8.
Native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
open MathlibExt.CategoryTheory.NativeScalarProjectionMaps

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X Y : Over B.analytic) (f : X ⟶ Y)
  (PX : AnalyticProObjectSites.PointRealization p X.left) (PY : AnalyticProObjectSites.PointRealization p Y.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left PX) CommRingCat.{1}] [HasSheafify (proTopology p Y.left PY) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)]
  [(etaleInclusion p Y.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).IsRightAdjoint]
  [((etaleInclusion p Y.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)).IsRightAdjoint]
  [IsIso (constantInverseMap (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (T := proTopology p X.left PX) (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [IsIso (constantInverseMap (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T := proTopology p Y.left PY) (etaleInclusion p Y.left) (WittVector p (BaseField.residueField p K)))]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify (proTopology p X.left PX) AddCommGrpCat.{1}]
  [(proTopology p X.left PX).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (SX : QualifiedStructuralPeriodSites.Source p K B X PX) (SY : QualifiedStructuralPeriodSites.Source p K B Y PY)
  (E : EtaleBaseChangeSource p f.left) (Q : ProBaseChangeSource p f.left E)
  [E.functor.IsContinuous (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)]
  [(E.functor.sheafPushforwardContinuous CommRingCat.{1} (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)).IsRightAdjoint]
  [Q.functor.IsContinuous (proTopology p Y.left PY) (proTopology p X.left PX)]
  [(Q.functor.sheafPushforwardContinuous CommRingCat.{1} (proTopology p Y.left PY) (proTopology p X.left PX)).IsRightAdjoint]
  (N : RingSquare (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left))

def basePeriod := inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.naiveStructuralFull
def baseScalar : ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q ⟶ basePeriod p K B X Y f PX PY SY E Q :=
  (Q.functor.sheafPullback CommRingCat.{1} (proTopology p Y.left PY) (proTopology p X.left PX)).map SY.scalars.originalToFull
def originalUnitY := inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular
def periodUnitY := inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.naiveStructuralFull

variable [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
  SX.regular (ProEtaleDeRhamSources.originalUnit p K B X PX SX)).IsRightAdjoint]
  (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p f.left SX.regularSheaf)
  (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p f.left SX.regularSheaf Ω)
  (D : AnalyticRelativeDeRhamSources.FilteredDeRhamSource p f.left E SX.regularSheaf SY.regularSheaf Ω M)
  [(modulePushforward (etaleInclusion p X.left)
    (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
      (T := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) E.functor (regularEtale p Y.left SY.regularSheaf))
    (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor
      (inverseRing (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
        (etaleInclusion p Y.left) (regularEtale p Y.left SY.regularSheaf)))
    (transferScalar (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
      (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
      (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
      E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
        (regularEtale p Y.left SY.regularSheaf))).IsRightAdjoint]
  [(cochainTransfer (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
      (regularEtale p Y.left SY.regularSheaf)).PreservesMonomorphisms]
  (DS : ProEtaleDeRhamSources.Source p K B X Y f PX PY SX SY E Q N Ω M D)
  (FS : ProEtaleDeRhamSources.FormSource p K B X Y f PX SX Ω)
  (hp : PositivePreservation p K B X Y f PX PY SX SY E)
  (PM : NaturalPeriodMaps p K B X Y f PX PY SX SY E Q N hp)
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.regular SX.naiveStructuralPositive
    SX.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.naiveStructuralPositive SX.naiveStructuralFull
    SX.scalars.positiveToFull).IsRightAdjoint]
  (PC : PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential)
  (FC : FullConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential PC)
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)).IsRightAdjoint]

def PeriodComplexType : Type _ :=
  MathlibExt.CategoryTheory.PeriodCoefficientComplexSources.Source
    Q.functor SY.naiveStructuralPositive SY.naiveStructuralFull p K SX.regular SX.positive SX.untilting SX.scalars
    PM.naiveStructuralPositive (NaturalPeriodMaps.structuralFullMap p K B X Y f PX PY SX SY E Q N hp PM)
    (ProEtaleDeRhamSources.coefficient p K B X Y f PX SX Ω M)
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential
    (ProEtaleDeRhamSources.Source.connection p K B X Y f PX PY SX SY E Q N Ω M D DS)
    PC FC (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N)
    (baseScalar p K B X Y f PX PY SY E Q)
    (ProEtaleDeRhamSources.native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
      (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total DS.terms

variable (PD : PeriodComplexType p K B X Y f PX PY SX SY E Q N Ω M D DS FS hp PM PC FC)
  [HasSheafify (proTopology p Y.left PY) AddCommGrpCat.{1}]
  [(proTopology p Y.left PY).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [EnoughInjectives (Modules SY.regular)] [EnoughInjectives (Modules SY.naiveStructuralFull)]
  [EnoughInjectives (Modules (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q))]
  [EnoughInjectives (Modules (basePeriod p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q)).IsRightAdjoint]
  [(pushforward Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.regular SY.naiveStructuralFull
    SY.scalars.originalToFull).IsRightAdjoint]
  [PullbackSourceUnit Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q)]
  [PullbackSourceUnit Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)]
  [PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)]
  (SC : SourceSquare Q.functor SY.regular SY.naiveStructuralFull
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q)
    SY.scalars.originalToFull (baseScalar p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q))
  (AO : DerivedAdjunctionSource Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q))
  (AP : DerivedAdjunctionSource Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q))
  (AS : DerivedAdjunctionSource (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q)
    (baseScalar p K B X Y f PX PY SY E Q))
  [PreservesFiniteLimits (scalarY SY.regular SY.naiveStructuralFull SY.scalars.originalToFull)]
  [PreservesFiniteColimits (scalarY SY.regular SY.naiveStructuralFull SY.scalars.originalToFull)]

def derivedComparison := MathlibExt.CategoryTheory.NativeRelativePeriodComparisonMaps.derivedComparison
  Q.functor SY.regular SY.naiveStructuralFull (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
  (basePeriod p K B X Y f PX PY SY E Q) SY.scalars.originalToFull (baseScalar p K B X Y f PX PY SY E Q)
  (originalUnitY p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q) SC AO AP AS
  (ProEtaleDeRhamSources.native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total PD.full PD.unit

def degreeComparison (i : ℤ) := MathlibExt.CategoryTheory.NativeRelativePeriodComparisonMaps.degreeComparison
  Q.functor SY.regular SY.naiveStructuralFull (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
  (basePeriod p K B X Y f PX PY SY E Q) SY.scalars.originalToFull (baseScalar p K B X Y f PX PY SY E Q)
  (originalUnitY p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q) SC AO AP AS
  (ProEtaleDeRhamSources.native (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)).total PD.full PD.unit i

end MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons
