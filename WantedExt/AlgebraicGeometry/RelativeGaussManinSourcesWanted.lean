/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
/-!
# Actual cofactor and higher Gauss--Manin proof requests

The cofactor uses the SAME original absolute associated coefficient,
actual native L² image/wedge/cokernel and original cotangent, tensor
and shift units. The finite-form projection is an explicitly guarded
IsIso conclusion. The higher connection is the COMPUTED native
boundary transport. Its Leibniz, literal curvature and Griffiths
properties are OUTPUT proofs, on native higher de Rham cohomology.

Source: Scholze, arXiv:1205.3463v2, Proposition 8.5 and Theorem 8.8(ii).

The exactness hypotheses (`PullbackSourceUnit`) and normalized derived adjunctions
(`DerivedAdjunctionSource`) below are all for module inverse images along the unit to an
inverse-image ring, which are exact; they are requested by
`RelativeIntegralPeriodComparisonWanted.inverseUnitPullbackExact` and
`inverseUnitDerivedAdjunction`. No request here assumes the exactness of a `B_dR⁺` or structural
period scalar extension. The exactness of restriction of scalars and of tensoring with the base
forms (`ExactCochainUnit`) is requested by `originalRestrictionExact` and `baseFormsTensorExact`
below.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RelativeGaussManinSources
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
open MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
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

include H
public theorem_wanted originalKScalarCompatibility (h : RelativeScope p B X Y f) :
  ScalarCompatibility (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H)

variable (hK : ScalarCompatibility (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H))

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

public def_wanted nativeBaseCotangentMap (h : RelativeScope p B X Y f) :
  { beta : BaseCotangentType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H) //
    CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
      (Ω := Ω) (FS := FS) (H := H) (beta := beta) }

variable (beta : BaseCotangentType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H))

public def_wanted nativeTwoBaseFormWedge (h : RelativeScope p B X Y f) :
  TwoBaseWedgeType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H) (beta := beta)

variable (W : TwoBaseWedgeType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H) (beta := beta))

public def_wanted originalGaussManinCofactor (h : RelativeScope p B X Y f)
    (hCotangent : CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
      (Ω := Ω) (FS := FS) (H := H) (beta := beta)) :
  QualifiedCofactorType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
    (Ω := Ω) (M := M) (D := D) (DS := DS) (H := H) (hK := hK) (beta := beta) (W := W)

variable (CB : CofactorType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
  (Ω := Ω) (M := M) (D := D) (H := H))
  (CQ : CofactorQualification (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
    (Ω := Ω) (M := M) (D := D) (DS := DS) (H := H) (hK := hK) (beta := beta) (W := W) (CB := CB))

variable [(NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY)).Additive]
  [PreservesFiniteLimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteColimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteLimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]
  [PreservesFiniteColimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]

/-- Restriction of scalars of modules from the inverse image of `O_Y` to the constant field `K` is
exact. -/
public def_wanted originalRestrictionExact (h : RelativeScope p B X Y f) :
    ExactCochainUnit (NativeRestrictionCohomologyMaps.restrictX (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (ax (E := E) (Q := Q) (H := H)))

/-- Tensoring with the inverse image of the absolute one-forms of `Y` is exact: they are locally
free, since `Y` is smooth (part of `RelativeScope`). -/
public def_wanted baseFormsTensorExact (h : RelativeScope p B X Y f) :
    ExactCochainUnit (NativeTensorProjectionMaps.tensorX Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))

variable [ExactCochainUnit (NativeRestrictionCohomologyMaps.restrictX (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (ax (E := E) (Q := Q) (H := H)))]
  [ExactCochainUnit (NativeTensorProjectionMaps.tensorX Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]

public def_wanted originalScalarRestrictionSquare (h : RelativeScope p B X Y f) :
  RestrictionSquareType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)

public def_wanted nativeBaseFormTensorSquare (h : RelativeScope p B X Y f) :
  TensorSquareType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)

variable (RS : RestrictionSquareType (E := E) (Q := Q) (H := H))
  (NS : TensorSquareType (E := E) (Q := Q) (H := H))
  (AO : DerivedAdjunctionSource Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular))

/-- Assemble the fixed native cofactor and finite-form projection before higher outputs. -/
public def_wanted originalGaussManinFactory (h : RelativeScope p B X Y f)
    (hForms : LocallyFiniteForms (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω))) :
  GaussManinFactory (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (H := H)

public theorem_wanted nativeFiniteFormsProjection (h : RelativeScope p B X Y f)
    (hForms : FiniteForms (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω))) (i : ℤ) :
  IsIso (gaussManinTarget (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (RS := RS) (NS := NS) (AO := AO) i)

/-- Native sheaf gluing retains locally varying form bounds over a non-quasi-compact base. -/
public theorem_wanted nativeLocallyFiniteFormsProjection (h : RelativeScope p B X Y f)
    (hForms : LocallyFiniteForms (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω))) (i : ℤ) :
  IsIso (gaussManinTarget (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (RS := RS) (NS := NS) (AO := AO) i)

variable (i : ℤ) [IsIso (gaussManinTarget (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (RS := RS) (NS := NS) (AO := AO) i)]
include CQ

public theorem_wanted higherGaussManinLeibniz (hBase : BaseData (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY)
  (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M))
    (hCotangent : CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
      (Ω := Ω) (FS := FS) (H := H) (beta := beta)) (hCofactor : CofactorQualification (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
    (Ω := Ω) (M := M) (D := D) (DS := DS) (H := H) (hK := hK) (beta := beta) (W := W) (CB := CB)) (h : RelativeScope p B X Y f) (hHigher : HigherLisseAt (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS) (T := T) (TQ := TQ) (L := L) i) :
  MathlibExt.CategoryTheory.NativeConnectionProperties.IsConnection (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) H.formSourceY.differential (higherConnection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (CB := CB) (RS := RS) (NS := NS) (AO := AO) i)

variable (D₁ : BaseOneFormType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (H := H))
  (W₁ : MathlibExt.CategoryTheory.NativeConnectionProperties.WedgeSource SY.regular (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))
  (N₁ : MathlibExt.CategoryTheory.NativeConnectionProperties.ExtensionSource (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (higherConnection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (CB := CB) (RS := RS) (NS := NS) (AO := AO) i) (MathlibExt.CategoryTheory.NativeConnectionProperties.FormDifferentialSource.sections (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) H.formSourceY.differential D₁.native) W₁)

public theorem_wanted higherGaussManinIntegrable (hBase : BaseData (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY)
  (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M))
    (hCotangent : CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
      (Ω := Ω) (FS := FS) (H := H) (beta := beta)) (hCofactor : CofactorQualification (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
    (Ω := Ω) (M := M) (D := D) (DS := DS) (H := H) (hK := hK) (beta := beta) (W := W) (CB := CB)) (h : RelativeScope p B X Y f) (hHigher : HigherLisseAt (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS) (T := T) (TQ := TQ) (L := L) i) :
  MathlibExt.CategoryTheory.NativeConnectionProperties.IsIntegrable (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (higherConnection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (CB := CB) (RS := RS) (NS := NS) (AO := AO) i) (MathlibExt.CategoryTheory.NativeConnectionProperties.FormDifferentialSource.sections (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) H.formSourceY.differential D₁.native) W₁ N₁

variable (HF : HigherFiltrationType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i)

public theorem_wanted higherGaussManinGriffiths (hBase : BaseData (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY)
  (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M))
    (hCotangent : CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
      (Ω := Ω) (FS := FS) (H := H) (beta := beta)) (hCofactor : CofactorQualification (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
    (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
    (Ω := Ω) (M := M) (D := D) (DS := DS) (H := H) (hK := hK) (beta := beta) (W := W) (CB := CB)) (h : RelativeScope p B X Y f) (hHigher : HigherLisseAt (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q) (N := N) (PS := PS) (T := T) (TQ := TQ) (L := L) i) :
  MathlibExt.CategoryTheory.NativeConnectionProperties.Griffiths (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources.higherDeRham (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (higherConnection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (CB := CB) (RS := RS) (NS := NS) (AO := AO) i) HF.filtration

end WantedExt.AlgebraicGeometry.RelativeGaussManinSources
