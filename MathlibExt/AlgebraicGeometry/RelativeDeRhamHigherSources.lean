/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison
public import MathlibExt.AlgebraicGeometry.ProEtaleIntegralLisseModules
public import MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons
public import MathlibExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources
public import MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation
public import MathlibExt.CategoryTheory.GaussManinCofactorNormalization

/-!
# Actual higher de Rham outputs and source-qualified BASE association

The integral local system is the native finite-image realization.
Its higher-lisse guard is local scalar extension of any finite Zp module
on ACTUAL native R^i f_*, including finite torsion coefficients.
BASE associated absolute coefficients may be input, as in Definition 7.5.
Their absolute cochains are fixed on all original continuous affinoid
connection units. The relative coefficient is the SAME original base
module and filtration, with its connection projected by the actual
cotangent map. No higher bundle, filtration, connection or comparison
is a field of BaseData.

Every higher carrier below is computed native derived cohomology; its
filtration uses native images of the transferred ORIGINAL filtered
complex, and Hodge boundaries use the native cochain cokernel triangle.

Source: Scholze, arXiv:1205.3463v2, Definitions 7.4--7.5,
Proposition 8.5 and Theorem 8.8; native Mathlib, Apache 2.0,
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources
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

def scalarX : Zhat p X.left PX ⟶ SX.absolutePositive :=
  IntegralWittSource.integralToPositive (p := p) (X := X.left) (P := PX) (Rplus := SX.positive)
    (W := IX) (A := SX.untilting)
def scalarY : Zhat p Y.left PY ⟶ SY.absolutePositive :=
  IntegralWittSource.integralToPositive (p := p) (X := Y.left) (P := PY) (Rplus := SY.positive)
    (W := IY) (A := SY.untilting)
def coefficientScalar := coefficientMap p K B X Y f PX PY E Q N PS ℤ_[p]

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

/-- The integral coefficient complex of `RelativeIntegralPeriodComparison`. -/
abbrev integralComplex : Derived (Zhat p X.left PX) :=
  RelativeIntegralPeriodComparison.integralComplex p K B X PX T TQ L

/-- The higher integral direct images of `RelativeIntegralPeriodComparison`. -/
abbrev higherIntegral (i : ℤ) : Modules (Zhat p Y.left PY) :=
  RelativeIntegralPeriodComparison.higherIntegral p K B X Y f PX PY E Q N PS T TQ L i

/-- The higher-lisse guard of integral relative 8.8, from `RelativeIntegralPeriodComparison`. -/
abbrev HigherLisseAt (i : ℤ) : Prop :=
  RelativeIntegralPeriodComparison.HigherLisseAt p K B X Y f PX PY E Q N PS T TQ L i

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

/-- Data making the integral local system `L` on $X$ associated, in the sense of Scholze
(arXiv:1205.3463, Definition 7.5), with a filtered vector bundle with connection on $X$ relative to
the base, whose relative version along `f` is the given coefficient `M`: differential forms of $X$
and of $Y$ over the base; the absolute coefficient, a filtered finite locally free module with
connection; a projection from the one-forms of $X$ over the base to the relative one-forms `Ω` of
`f`, compatible with the differentials, through which the relative coefficient of the absolute one
is `M`; the scalar, form, cochain, filtration and connection data on $X$ and $Y$ that this uses; and
the association, an isomorphism between `L` and the absolute coefficient after extension of scalars
to the period sheaf, compatible with filtrations and connections
(`BaseFilteredPeriodAssociation.Associated`). -/
structure BaseData where
  absoluteFormsX : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom SX.regularSheaf
  absoluteFormsY : AnalyticRelativeDeRhamSources.DifferentialSource p Y.hom SY.regularSheaf
  absoluteCoefficient : AnalyticRelativeDeRhamSources.BaseCoefficientInput p X.hom SX.regularSheaf absoluteFormsX
  relativeProjection : absoluteFormsX.oneForms ⟶ Ω.oneForms
  relativeProjection_differential : ∀ (U : (AnalyticProObjectSites.Etale p X.left)ᵒᵖ)
    (a : (regularEtale p X.left SX.regularSheaf).obj.obj U),
    (relativeProjection.val.app U).hom (absoluteFormsX.differential U a) = Ω.differential U a
  relativeInput : AnalyticRelativeDeRhamSources.RelativeCoefficientInputSource
    (p := p) (B := B) (Z := X) (hZ := SX.regularSheaf) (g := f.left)
    (ΩA := absoluteFormsX) (ΩR := Ω) (M := absoluteCoefficient) (ρ := relativeProjection)
  relative_input_source : relativeInput.relative = M
  scalarX : AnalyticAbsoluteDeRhamSources.EtaleKScalarSource p K B X PX SX
  scalarY : AnalyticAbsoluteDeRhamSources.EtaleKScalarSource p K B Y PY SY
  formSourceX : AnalyticPerfectoidPeriodCharts.AbsoluteFormSource p K B X PX SX absoluteFormsX
  formSourceY : AnalyticPerfectoidPeriodCharts.AbsoluteFormSource p K B Y PY SY absoluteFormsY
  absoluteCochains : AnalyticAbsoluteDeRhamSources.AbsoluteComplexSource p K B X PX SX
    absoluteFormsX absoluteCoefficient scalarX
  baseFiltration : AnalyticAbsoluteDeRhamSources.FiltrationSource p K B X PX SX absoluteFormsX absoluteCoefficient
  positiveConnectionX : PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX absoluteFormsX) formSourceX.differential
  fullConnectionX : FullConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX absoluteFormsX) formSourceX.differential positiveConnectionX
  positiveConnectionY : PositiveConnectionSource p K SY.regular SY.positive SY.untilting SY.scalars
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY absoluteFormsY) formSourceY.differential
  fullConnectionY : FullConnectionSource p K SY.regular SY.positive SY.untilting SY.scalars
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY absoluteFormsY) formSourceY.differential positiveConnectionY
  baseConnection : MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation.CoefficientConnectionSource
    p K SX.regular SX.positive SX.untilting SX.scalars
    (AnalyticAbsoluteDeRhamSources.coefficient p K B X PX SX absoluteFormsX absoluteCoefficient)
    (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX absoluteFormsX)
    formSourceX.differential absoluteCochains.connection positiveConnectionX fullConnectionX
  association : MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation.Associated
    p K SX.regular SX.positive (Zhat p X.left PX) SX.untilting SX.scalars
    (MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison.scalarX
      (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (FX := FX) (IX := IX)) L.module
    (AnalyticAbsoluteDeRhamSources.coefficient p K B X PX SX absoluteFormsX absoluteCoefficient)
    (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX absoluteFormsX) baseFiltration.filtration
    formSourceX.differential absoluteCochains.connection positiveConnectionX fullConnectionX baseConnection

variable [EnoughInjectives (Modules SY.regular)]
  [EnoughInjectives (Modules (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q))]
  [(pushforward Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)).IsRightAdjoint]

abbrev nativeRelative := ProEtaleDeRhamSources.native
  (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
  (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)

abbrev higherDeRham (i : ℤ) := ProEtaleDeRhamSources.higherDeRham
  (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
  (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i

abbrev higherHodge (i j : ℤ) := ProEtaleDeRhamSources.higherHodge
  (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
  (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) i j

abbrev HigherFiltrationType (i : ℤ) := HigherFiltrationSource Q.functor SY.regular
  (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
  (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  (nativeRelative (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) i

abbrev GradedExactType := GradedExactSource
  (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
  (nativeRelative (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D))

abbrev hodgeBoundary (GE : GradedExactType
    (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) (i j : ℤ) :=
  gradedBoundary Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
    (nativeRelative (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
      (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)) GE i j

end MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources
