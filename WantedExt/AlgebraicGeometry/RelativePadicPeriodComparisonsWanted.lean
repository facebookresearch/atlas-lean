/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons

/-!
# Source-qualified native coherent relative period comparison

The proper smooth map is actual analytic geometry over the original
complete discretely valued K/Q_p with perfect residue field. All original,
period and cochain objects and all comparison arrows are native fixed
constructions. These coherent-comparison requests are Lemma 8.6 and the
coherent step in Theorem 8.8; they make no unrestricted rational lisse
Theorem 8.8 assertion. Full Qhat objects remain available independently.

Positive period cochains use original O_X tensor and the total relative
connection; full cochains use local absolute theta-generator fractions.
Provider construction/proof availability is separate from interface coverage.

Source: Scholze, arXiv:1205.3463v2, Proposition 8.5, Lemma 8.6 and
Theorem 8.8. Completed Stacks 07I0 source at Atlas PR2245
`76de3f2665f9c44b06932f9861ee9aae65e04395`, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativePadicPeriodComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
open MathlibExt.CategoryTheory.NativeScalarProjectionMaps

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
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.regular SX.structuralPositive
    SX.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.structuralPositive SX.structuralFull
    SX.scalars.positiveToFull).IsRightAdjoint]
  (PC : PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential)
  (FC : FullConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential PC)
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)).IsRightAdjoint]

/-- Construct positive coefficient cochains and full local-generator-fraction cochains, with the ORIGINAL unit fixed in every degree. -/
public def_wanted relativePeriodCoefficientComplex (h : RelativeScope p B X Y f) :
  PeriodComplexType p K B X Y f PX PY SX SY E Q N Ω M D DS FS hp PM PC FC

variable (PD : PeriodComplexType p K B X Y f PX PY SX SY E Q N Ω M D DS FS hp PM PC FC)
  [HasSheafify (proTopology p Y.left PY) AddCommGrpCat.{1}]
  [(proTopology p Y.left PY).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [EnoughInjectives (Modules SY.regular)] [EnoughInjectives (Modules SY.structuralFull)]
  [EnoughInjectives (Modules (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q))]
  [EnoughInjectives (Modules (basePeriod p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q)).IsRightAdjoint]
  [(pushforward Q.functor SY.structuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.regular SY.structuralFull
    SY.scalars.originalToFull).IsRightAdjoint]
  [PullbackSourceUnit Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q)]
  [PullbackSourceUnit Q.functor SY.structuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)]
  [PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)]
  (SC : SourceSquare Q.functor SY.regular SY.structuralFull
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q)
    SY.scalars.originalToFull (baseScalar p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q))
  (AO : DerivedAdjunctionSource Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (originalUnitY p K B X Y f PX PY SY E Q))
  (AP : DerivedAdjunctionSource Q.functor SY.structuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q))
  (AS : DerivedAdjunctionSource (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q)
    (baseScalar p K B X Y f PX PY SY E Q))
  [PreservesFiniteLimits (scalarY SY.regular SY.structuralFull SY.scalars.originalToFull)]
  [PreservesFiniteColimits (scalarY SY.regular SY.structuralFull SY.scalars.originalToFull)]

/-- The actual native derived comparison; its IsIso is a CONCLUSION. Locally finite form bounds cover a non-quasi-compact base. -/
public proof_wanted coherentDerivedPeriodComparison (h : RelativeScope p B X Y f)
    (hForms : MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.LocallyFiniteForms
      (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω)) :
  IsIso (MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons.derivedComparison
    (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)
    (DS := DS) (FS := FS) (hp := hp) (PM := PM) (PC := PC) (FC := FC) (PD := PD)
    (SC := SC) (AO := AO) (AP := AP) (AS := AS))

/-- The canonical native higher map to the constructed period-cohomology target. -/
public proof_wanted coherentDegreePeriodComparison (h : RelativeScope p B X Y f)
    (hForms : MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.LocallyFiniteForms
      (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω)) (i : ℤ) :
  IsIso (MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons.degreeComparison
    (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)
    (DS := DS) (FS := FS) (hp := hp) (PM := PM) (PC := PC) (FC := FC) (PD := PD)
    (SC := SC) (AO := AO) (AP := AP) (AS := AS) i)

end WantedExt.AlgebraicGeometry.RelativePadicPeriodComparisons
