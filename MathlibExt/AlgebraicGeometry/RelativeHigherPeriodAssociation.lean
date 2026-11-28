/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
public import MathlibExt.CategoryTheory.AssociatedPeriodAugmentationSources
public import MathlibExt.CategoryTheory.NativeScalarCompositionSources
/-!
# Constructed integral higher filtered period association

Both the actual integral native R^i f_* coefficient and actual relative
native R^i f_dR* coefficient map to the SAME constructed period-complex
cohomology. The source lisse augmentation is fixed on every original
coefficient by the given BASE association. Higher bundles and filtrations are
OUTPUT carriers, never replacement input data.

The canonical higher comparison (the composition of those native maps with the inverse of the
coherent period comparison) and the associated filtered bundle are not constructed here: the
period objects are the naive structural periods of `StructuralDeRhamPeriodSources` (Scholze's
withdrawn Definition 6.8, erratum item (3)), for which the coherent comparison is not available.
They await the corrected finite-stage construction.

Source: Scholze, arXiv:1205.3463v2, Definitions 7.5 and 8.3 and Theorem 8.8.
Native Mathlib, Apache 2.0, `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RelativeHigherPeriodAssociation
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources
open MathlibExt.CategoryTheory
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open AnalyticCoefficientPeriodScalars
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
attribute [local instance] HasDerivedCategory.standard
open MathlibExt.CategoryTheory.RingSheafModuleTensors
open MathlibExt.CategoryTheory.NativeGaussManinOutputs
open MathlibExt.CategoryTheory.NativeRestrictionCohomologyMaps
open MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons
open MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
open MathlibExt.CategoryTheory.NativeScalarCompositionSources
variable (p : ℕ) [Fact p.Prime]

variable (K : BaseField p) (B : BaseRealization p K) (X Y : Over B.analytic) (f : X ⟶ Y)
  (PX : AnalyticProObjectSites.PointRealization p X.left)
  (PY : AnalyticProObjectSites.PointRealization p Y.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left PX) CommRingCat.{1}]
  [HasSheafify (proTopology p Y.left PY) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)]
  [(etaleInclusion p Y.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).IsRightAdjoint]
  [((etaleInclusion p Y.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (proTopology p Y.left PY)).IsRightAdjoint]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left PX)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
    (etaleInclusion p Y.left) (WittVector p (BaseField.residueField p K)))]
  (SX : Source p K B X PX) (SY : Source p K B Y PY)
  (E : EtaleBaseChangeSource p f.left) (Q : ProBaseChangeSource p f.left E)
  [E.functor.IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)]
  [(E.functor.sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)).IsRightAdjoint]
  [Q.functor.IsContinuous (proTopology p Y.left PY) (proTopology p X.left PX)]
  [(Q.functor.sheafPushforwardContinuous CommRingCat.{1}
    (proTopology p Y.left PY) (proTopology p X.left PX)).IsRightAdjoint]
  (N : RingSquare
    (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left))

variable (PS : PointProjectionSource p K B X Y f PX PY E Q N)
  (hp : PositivePreservation p K B X Y f PX PY SX SY E)
  (PM : NaturalPeriodMaps p K B X Y f PX PY SX SY E Q N hp)
  (FX : PrimeTiltSource p X.left PX SX.positive) (FY : PrimeTiltSource p Y.left PY SY.positive)
  (IX : IntegralWittSource p X.left PX SX.positive FX) (IY : IntegralWittSource p Y.left PY SY.positive FY)
  [HasSheafify (proTopology p X.left PX) AddCommGrpCat.{1}]
  [(proTopology p X.left PX).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify (proTopology p Y.left PY) AddCommGrpCat.{1}]
  [(proTopology p Y.left PY).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [∀ U : AnalyticProObjectSites.ProEtaleSite p Y.left,
    HasWeakSheafify ((proTopology p Y.left PY).over U) AddCommGrpCat.{1}]
  [∀ U : AnalyticProObjectSites.ProEtaleSite p Y.left,
    ((proTopology p Y.left PY).over U).WEqualsLocallyBijective AddCommGrpCat.{1}]

variable [∀ U : AnalyticProObjectSites.Etale p X.left,
  (Over.forget U).IsContinuous ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).over U)
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)]
  [∀ U : AnalyticProObjectSites.Etale p X.left,
    HasSheafify ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).over U) (ModuleCat.{1} ℤ_[p])]
  [((etaleInclusion p X.left).sheafPushforwardContinuous (ModuleCat.{1} ℤ_[p])
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left PX)).IsRightAdjoint]
  [Abelian (ProEtaleIntegralTowers.ProCoefficients p X.left PX)]
  [EnoughInjectives (ℕᵒᵖ ⥤ ProEtaleIntegralTowers.ProCoefficients p X.left PX)]
  [HasLimitsOfShape (Discrete ℕ) (ProEtaleIntegralTowers.ProCoefficients p X.left PX)]
  (T : ProEtaleIntegralTowers.LisseIntegralTower p X.left)
  (TQ : MathlibExt.CategoryTheory.ResolvedFiniteInverseImages.Qualification
    (ProEtaleIntegralTowers.finiteInverseImage p X.left PX) T.tower)
  (L : ProEtaleIntegralTowers.IntegralRealizationSource p X.left PX T TQ)
  [(pushforward Q.functor (Zhat p Y.left PY) (Zhat p X.left PX)
    (coefficientScalar p K B X Y f PX PY E Q N PS)).IsRightAdjoint]
  [(pushforward Q.functor SY.absolutePositive SX.absolutePositive PM.absolutePositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) (Zhat p Y.left PY) SY.absolutePositive
    (scalarY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (Zhat p X.left PX) SX.absolutePositive
    (scalarX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX))).IsRightAdjoint]
  [EnoughInjectives (Modules (Zhat p X.left PX))] [EnoughInjectives (Modules (Zhat p Y.left PY))]
  [EnoughInjectives (Modules SX.absolutePositive)] [EnoughInjectives (Modules SY.absolutePositive)]
  [PullbackSourceUnit Q.functor (Zhat p Y.left PY) (Zhat p X.left PX)
    (coefficientScalar p K B X Y f PX PY E Q N PS)]

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

variable [(modulePushforward (etaleInclusion p Y.left) (regularEtale p Y.left SY.regularSheaf)
  SY.regular (AnalyticPerfectoidPeriodCharts.originalRingUnit p K B Y PY SY)).IsRightAdjoint]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left PX)
    (etaleInclusion p X.left) (BaseField.carrier p K))]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left) (T := proTopology p Y.left PY)
    (etaleInclusion p Y.left) (BaseField.carrier p K))]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.regular SX.naiveStructuralPositive
    SX.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.naiveStructuralPositive SX.naiveStructuralFull
    SX.scalars.positiveToFull).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.absolutePositive SX.naiveStructuralFull
    (SX.scalars.absoluteToPositive ≫ SX.scalars.positiveToFull)).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.regular SY.naiveStructuralPositive
    SY.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.naiveStructuralPositive SY.naiveStructuralFull
    SY.scalars.positiveToFull).IsRightAdjoint]

local instance originalModulePullbackX :
    (modulePushforward (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
      SX.regular (AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X PX SX)).IsRightAdjoint := by
  change (modulePushforward (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
    SX.regular (ProEtaleDeRhamSources.originalUnit p K B X PX SX)).IsRightAdjoint
  infer_instance

variable [EnoughInjectives (Modules SY.regular)]
  [EnoughInjectives (Modules (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)).IsRightAdjoint]

variable (H : BaseData (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY)
  (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M))

variable [IsIso (constantInverseMap (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
  Q.functor (BaseField.carrier p K))]

variable [PullbackSourceUnit Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)]
  [(pushforward Q.functor (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY)
    (AnalyticAbsoluteDeRhamSources.constantK p K B X PX)
    (constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K))).IsRightAdjoint]
  [EnoughInjectives (Modules (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY))]
  [EnoughInjectives (Modules (AnalyticAbsoluteDeRhamSources.constantK p K B X PX))]
  [(NativeTensorProjectionMaps.tensorX Q.functor SY.regular
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)).Additive]
  [(NativeTensorProjectionMaps.tensorY SY.regular
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)).Additive]
  [(NativeRestrictionCohomologyMaps.restrictX (AnalyticAbsoluteDeRhamSources.constantK p K B X PX)
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (ax (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H))).Additive]

variable [(NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY)).Additive]
  [PreservesFiniteLimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteColimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteLimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]
  [PreservesFiniteColimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]
  [ExactCochainUnit (NativeRestrictionCohomologyMaps.restrictX (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (ax (E := E) (Q := Q) (H := H)))]
  [ExactCochainUnit (NativeTensorProjectionMaps.tensorX Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]

variable (PC : PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential)
  (FC : FullConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential PC)
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)).IsRightAdjoint]

def absoluteToFullX : SX.absolutePositive ⟶ SX.naiveStructuralFull :=
  SX.scalars.absoluteToPositive ≫ SX.scalars.positiveToFull

def absoluteToFullY : SY.absolutePositive ⟶ SY.naiveStructuralFull :=
  SY.scalars.absoluteToPositive ≫ SY.scalars.positiveToFull

def zFullX : Zhat p X.left PX ⟶ SX.naiveStructuralFull :=
  MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison.scalarX
    (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX) ≫
      absoluteToFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX)

def zFullY : Zhat p Y.left PY ⟶ SY.naiveStructuralFull :=
  MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison.scalarY
    (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY) ≫
      absoluteToFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY)

def baseZ := inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (Zhat p Y.left PY)
def baseZUnit := inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (Zhat p Y.left PY)
def baseZScalar := inverseScalar (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor
  (Zhat p Y.left PY) (Zhat p X.left PX) (coefficientScalar p K B X Y f PX PY E Q N PS)
def basePeriodZ : baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) ⟶
    basePeriod p K B X Y f PX PY SY E Q :=
  (Q.functor.sheafPullback CommRingCat.{1} (proTopology p Y.left PY) (proTopology p X.left PX)).map
    (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))

variable [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (Zhat p X.left PX) SX.naiveStructuralFull
    (zFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX))).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) (Zhat p Y.left PY) SY.naiveStructuralFull
    (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.absolutePositive SY.naiveStructuralFull
    (absoluteToFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY))).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p Y.left)) SY.regular SY.naiveStructuralFull SY.scalars.originalToFull).IsRightAdjoint]
  [EnoughInjectives (Modules SY.naiveStructuralFull)]
  [EnoughInjectives (Modules (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)))]
  [EnoughInjectives (Modules (basePeriod p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor (Zhat p Y.left PY)
    (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))
    (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))).IsRightAdjoint]
  [(pushforward Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))
    (basePeriod p K B X Y f PX PY SY E Q)
    (basePeriodZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) (FY := FY) (IY := IY))).IsRightAdjoint]

variable (CLX : CompositionSource (Zhat p X.left PX) SX.absolutePositive SX.naiveStructuralFull
    (MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison.scalarX
      (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX))
    (absoluteToFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX)))
  (CLY : CompositionSource (Zhat p Y.left PY) SY.absolutePositive SY.naiveStructuralFull
    (MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison.scalarY
      (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))
    (absoluteToFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY)))
  (CEY : CompositionSource SY.regular SY.naiveStructuralPositive SY.naiveStructuralFull
    SY.scalars.originalToPositive SY.scalars.positiveToFull)

/-- The given BASE association carried to the SAME actual relative period coefficient. -/
def baseDirectAssociation :
    AssociatedPeriodAugmentationSources.fullCoefficient (Zhat p X.left PX) SX.naiveStructuralFull
      (zFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX)) L.module ≅
    fullForms p K SX.regular SX.positive SX.untilting SX.scalars
      (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)) :=
  CLX.iso.app L.module ≪≫ H.association.comparison ≪≫
    (pullback (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.naiveStructuralPositive SX.naiveStructuralFull
      SX.scalars.positiveToFull).mapIso
        ((pullback (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.regular SX.naiveStructuralPositive
          SX.scalars.originalToPositive).mapIso
            (RelativeGaussManinSources.absoluteCoefficientIso (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
              (PX := PX) (PY := PY) (SX := SX) (SY := SY) (Ω := Ω) (M := M) (H := H)).symm)

variable (PD : PeriodComplexType p K B X Y f PX PY SX SY E Q N Ω M D DS FS hp PM PC FC)

abbrev AugmentationType := AssociatedPeriodAugmentationSources.Source
  Q.functor (Zhat p Y.left PY) SY.naiveStructuralFull (Zhat p X.left PX) SX.naiveStructuralFull
  (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))
  (coefficientScalar p K B X Y f PX PY E Q N PS)
  (zFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX)) L.module
  (fullForms p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)))
  (fullForms p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)))
  (baseDirectAssociation (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (Ω := Ω) (M := M) (H := H) (CLX := CLX)) PD.full
  (PeriodCoefficientComplexSources.fullBaseMap Q.functor SY.naiveStructuralFull p K SX.regular SX.positive SX.untilting SX.scalars
    (NaturalPeriodMaps.structuralFullMap p K B X Y f PX PY SX SY E Q N hp PM)) PD.fullTerms

variable [PullbackSourceUnit Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q)]
  [PullbackSourceUnit Q.functor (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))]
  [PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (basePeriod p K B X Y f PX PY SY E Q) (basePeriodZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) (FY := FY) (IY := IY))]
  [PreservesFiniteLimits (NativeScalarProjectionMaps.scalarY SY.regular SY.naiveStructuralFull SY.scalars.originalToFull)]
  [PreservesFiniteColimits (NativeScalarProjectionMaps.scalarY SY.regular SY.naiveStructuralFull SY.scalars.originalToFull)]
  [PreservesFiniteLimits (NativeScalarProjectionMaps.scalarY (Zhat p Y.left PY) SY.naiveStructuralFull (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY)))]
  [PreservesFiniteColimits (NativeScalarProjectionMaps.scalarY (Zhat p Y.left PY) SY.naiveStructuralFull (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY)))]

local instance coherentOriginalPullbackUnit :
    PullbackSourceUnit Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
      (originalUnitY p K B X Y f PX PY SY E Q) := by
  change PullbackSourceUnit Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  infer_instance

local instance augmentationBaseInjectives : EnoughInjectives (Modules
    (AssociatedPeriodAugmentationSources.baseAbsolute (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
      Q.functor (Zhat p Y.left PY))) := by
  change EnoughInjectives (Modules (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (E := E) (Q := Q)))
  infer_instance

local instance augmentationPeriodInjectives : EnoughInjectives (Modules
    (AssociatedPeriodAugmentationSources.basePeriod (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
      Q.functor SY.naiveStructuralFull)) := by
  change EnoughInjectives (Modules (basePeriod p K B X Y f PX PY SY E Q))
  infer_instance

local instance augmentationBasePullbackUnit :
    PullbackSourceUnit Q.functor (Zhat p Y.left PY)
      (AssociatedPeriodAugmentationSources.baseAbsolute (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
        Q.functor (Zhat p Y.left PY))
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (Zhat p Y.left PY)) := by
  change PullbackSourceUnit Q.functor (Zhat p Y.left PY)
    (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))
    (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))
  infer_instance

local instance augmentationPeriodPullbackUnit :
    PullbackSourceUnit Q.functor SY.naiveStructuralFull
      (AssociatedPeriodAugmentationSources.basePeriod (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
        Q.functor SY.naiveStructuralFull)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.naiveStructuralFull) := by
  change PullbackSourceUnit Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q)
    (periodUnitY p K B X Y f PX PY SY E Q)
  infer_instance

local instance augmentationScalarPullbackUnit :
    PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
      (AssociatedPeriodAugmentationSources.baseAbsolute (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
        Q.functor (Zhat p Y.left PY))
      (AssociatedPeriodAugmentationSources.basePeriod (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
        Q.functor SY.naiveStructuralFull)
      (AssociatedPeriodAugmentationSources.scalar (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
        Q.functor (Zhat p Y.left PY) SY.naiveStructuralFull
          (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY))) := by
  change PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left))
    (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))
    (basePeriod p K B X Y f PX PY SY E Q)
    (basePeriodZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) (FY := FY) (IY := IY))
  infer_instance

/-! The coherent comparison below also uses the derived scalar extension along `baseScalar`
(from the inverse image of `O_Y` to that of the naive structural periods), whose exactness
(`PullbackSourceUnit`, a flatness statement) is a hypothesis here and is not requested. -/

variable [PullbackSourceUnit (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q)]

variable (SO : NativeScalarProjectionMaps.SourceSquare Q.functor SY.regular SY.naiveStructuralFull
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q) SY.scalars.originalToFull (baseScalar p K B X Y f PX PY SY E Q) (originalUnitY p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q))
  (AZO : DerivedAdjunctionSource Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (originalUnitY p K B X Y f PX PY SY E Q))
  (AZF : DerivedAdjunctionSource Q.functor SY.naiveStructuralFull (basePeriod p K B X Y f PX PY SY E Q) (periodUnitY p K B X Y f PX PY SY E Q))
  (ASO : DerivedAdjunctionSource (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (basePeriod p K B X Y f PX PY SY E Q) (baseScalar p K B X Y f PX PY SY E Q))
  (SZ : NativeScalarProjectionMaps.SourceSquare Q.functor (Zhat p Y.left PY) SY.naiveStructuralFull (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (basePeriod p K B X Y f PX PY SY E Q) (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY)) (basePeriodZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) (FY := FY) (IY := IY)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (periodUnitY p K B X Y f PX PY SY E Q))
  (AZZ : DerivedAdjunctionSource Q.functor (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)))
  (ASZ : DerivedAdjunctionSource (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (basePeriod p K B X Y f PX PY SY E Q) (basePeriodZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) (FY := FY) (IY := IY)))
  (AL : AugmentationType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (hp := hp) (PM := PM) (PC := PC) (FC := FC) (PD := PD) (FX := FX) (FY := FY) (IX := IX) (IY := IY) (PS := PS) (T := T) (TQ := TQ) (L := L) (H := H) (CLX := CLX))

/-- The original coherent cochain unit and native derived scalar projection. -/
def coherentPeriodComparison (i : ℤ) := RelativePadicPeriodComparisons.degreeComparison
  (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (hp := hp) (PM := PM) (PC := PC) (FC := FC) (PD := PD) (SC := SO) (AO := AZO) (AP := AZF) (AS := ASO) i

/-- The lisse comparison is constructed from the normalized BASE association augmentation. -/
def lissePeriodComparison (i : ℤ) := AssociatedPeriodAugmentationSources.comparison
  Q.functor (Zhat p Y.left PY) SY.naiveStructuralFull (Zhat p X.left PX) SX.naiveStructuralFull (zFullY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (FY := FY) (IY := IY)) (coefficientScalar p K B X Y f PX PY E Q N PS) (zFullX (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX)) L.module
  (fullForms p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)))
  (fullForms p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)))
  (baseDirectAssociation (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (Ω := Ω) (M := M) (H := H) (CLX := CLX)) PD.full
  (PeriodCoefficientComplexSources.fullBaseMap Q.functor SY.naiveStructuralFull p K SX.regular SX.positive SX.untilting SX.scalars
    (NaturalPeriodMaps.structuralFullMap p K B X Y f PX PY SX SY E Q N hp PM)) PD.fullTerms AL SZ AZZ AZF ASZ i

local instance originalZRestrictionAdditive :
    (NativeRestrictionCohomologyMaps.restrictX (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (Zhat p X.left PX) (baseZScalar (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS))).Additive := by
  unfold NativeRestrictionCohomologyMaps.restrictX NativeFilteredDeRhamOutputs.restrict
  infer_instance

variable [PreservesFiniteLimits (NativeRestrictionCohomologyMaps.restrictY (Zhat p Y.left PY) (Zhat p Y.left PY) (𝟙 (Zhat p Y.left PY)))]
  [PreservesFiniteColimits (NativeRestrictionCohomologyMaps.restrictY (Zhat p Y.left PY) (Zhat p Y.left PY) (𝟙 (Zhat p Y.left PY)))]
  [ExactCochainUnit (NativeRestrictionCohomologyMaps.restrictX (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (Zhat p X.left PX) (baseZScalar (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS)))]
  (RZ : NativeRestrictionCohomologyMaps.SourceSquare Q.functor (Zhat p Y.left PY) (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (Zhat p X.left PX) (𝟙 (Zhat p Y.left PY)) (baseZScalar (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (coefficientScalar p K B X Y f PX PY E Q N PS))
  (IDZ : IdentityRestrictionSource (Zhat p Y.left PY))
  (SSZ : SingleRestrictionSource (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (Zhat p X.left PX) (baseZScalar (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS)))

/-- Native higher restriction from ACTUAL R^i f_* L to the degree-zero source of the
augmentation, using only native single/quotient/derived-unit factors. -/
def higherZRestriction (i : ℤ) : (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherIntegral (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS) (T := T) (TQ := TQ) (L := L) i) ⟶
    cohomology (Zhat p Y.left PY) ((derivedPushforward Q.functor (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))).obj
      (DerivedCategory.Plus.Q.obj (AssociatedPeriodAugmentationSources.coefficientComplex Q.functor (Zhat p Y.left PY) (Zhat p X.left PX) (coefficientScalar p K B X Y f PX PY E Q N PS) L.module))) i :=
  (DerivedCategory.Plus.homologyFunctor (Modules (Zhat p Y.left PY)) i).map
    ((derivedPushforward Q.functor (Zhat p Y.left PY) (Zhat p X.left PX) (coefficientScalar p K B X Y f PX PY E Q N PS)).map
      (NativeScalarCompositionSources.singleDerivedIso (Zhat p X.left PX) L.module).inv) ≫
  IDZ.iso.hom.app (cohomology (Zhat p Y.left PY) ((derivedPushforward Q.functor (Zhat p Y.left PY) (Zhat p X.left PX) (coefficientScalar p K B X Y f PX PY E Q N PS)).obj
      (DerivedCategory.Plus.Q.obj (NativeScalarCompositionSources.single (Zhat p X.left PX) L.module))) i) ≫
  NativeRestrictionCohomologyMaps.cohomologyMap Q.functor (Zhat p Y.left PY) (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (Zhat p X.left PX) (𝟙 (Zhat p Y.left PY)) (baseZScalar (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (coefficientScalar p K B X Y f PX PY E Q N PS) RZ (NativeScalarCompositionSources.single (Zhat p X.left PX) L.module) i ≫
  (DerivedCategory.Plus.homologyFunctor (Modules (Zhat p Y.left PY)) i).map
    ((derivedPushforward Q.functor (Zhat p Y.left PY) (baseZ (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)) (baseZUnit (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q))).map
      (DerivedCategory.Plus.Q.map (SSZ.iso L.module).hom))

variable (GM : RelativeGaussManinSources.GaussManinFactory (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (H := H))

/-- The connection on the actual higher carrier is the computed native Gauss--Manin map. -/
def higherNabla (i : ℤ) (U : (AnalyticProObjectSites.ProEtaleSite p Y.left)ᵒᵖ) :
    (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i).val.obj U →+ (tensor SY.regular (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)).val.obj U :=
  ((RelativeGaussManinSources.GaussManinFactory.connection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (H := H) (S := GM) i).val.app U).hom.toAddMonoidHom

/-- The period coefficient connection is a source OUTPUT on the computed higher module,
normalized on every original coefficient and full local-generator fraction. -/
abbrev HigherCoefficientConnectionType (i : ℤ) := BaseFilteredPeriodAssociation.CoefficientConnectionSource
  p K SY.regular SY.positive SY.untilting SY.scalars (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)
    H.formSourceY.differential (higherNabla (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (H := H) (GM := GM) i) H.positiveConnectionY H.fullConnectionY

end MathlibExt.AlgebraicGeometry.RelativeHigherPeriodAssociation
