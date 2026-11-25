/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeDeRhamHigherSources
/-!
# Source-qualified native relative Gauss--Manin outputs

The original absolute coefficient cochain is the SAME BASE associated
coefficient as the transferred relative complex. The absolute terms
below use only the native original coefficient identification. The
native L² cofactor is normalized on every original form/tensor/shift
unit. Its actual cochain boundary constructs the higher connection.
No higher flat bundle or arbitrarily chosen absolute complex is input.

Source: Scholze, arXiv:1205.3463v2, Proposition 8.5 and Theorem 8.8;
Stacks Tags 07HY and 07I0; native Mathlib, Apache 2.0,
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
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

abbrev G := Q.functor
abbrev OY := SY.regular
abbrev OX := SX.regular
abbrev RX := ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q
abbrev eta := ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N
abbrev s := inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular
abbrev KY := AnalyticAbsoluteDeRhamSources.constantK p K B Y PY
abbrev KX := AnalyticAbsoluteDeRhamSources.constantK p K B X PX
abbrev ay := AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY
abbrev k := constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K)
abbrev omegaY := AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY
abbrev omegaA := AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX
abbrev omegaR := ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)
abbrev coefficient := ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)
abbrev F := nativeRelative (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)

variable [IsIso (constantInverseMap (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
  Q.functor (BaseField.carrier p K))]

/-- Actual K_X -> f^-1 O_Y, through the native constant inverse-image comparison. -/
def ax : KX (p := p) (K := K) (B := B) (X := X) (PX := PX) ⟶
    RX (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q) :=
  inv (constantInverseMap (J := proTopology p Y.left PY) (T := proTopology p X.left PX)
    Q.functor (BaseField.carrier p K)) ≫
  (Q.functor.sheafPullback CommRingCat.{1} (proTopology p Y.left PY) (proTopology p X.left PX)).map
    (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY)

abbrev etaX := eta (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N)
abbrev axX := ax (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)
abbrev omY := omegaY (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (H := H)
abbrev omA := omegaA (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (H := H)
abbrev omR := omegaR (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)
abbrev EPro := coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)
abbrev DR := F (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D)
abbrev kyRing := KY (p := p) (K := K) (B := B) (Y := Y) (PY := PY)
abbrev kxRing := KX (p := p) (K := K) (B := B) (X := X) (PX := PX)
abbrev ayY := ay (p := p) (K := K) (B := B) (Y := Y) (PY := PY) (SY := SY) (H := H)
abbrev kMap := k (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (E := E) (Q := Q)
abbrev sMap := s (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q)
abbrev rRing := RX (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SY := SY) (E := E) (Q := Q)

/-- The original native inverse-image coefficient identification, from the SAME etale module. -/
def absoluteCoefficientIso : EPro (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M) ≅
    AnalyticAbsoluteDeRhamSources.coefficient p K B X PX SX H.absoluteFormsX H.absoluteCoefficient := by
  have hm : M.module = H.absoluteCoefficient.module := by
    exact (congrArg
      (fun N₀ : AnalyticRelativeDeRhamSources.BaseCoefficientInput p f.left SX.regularSheaf Ω => N₀.module)
      H.relative_input_source).symm.trans H.relativeInput.module_source
  exact (modulePullback (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
    SX.regular (ProEtaleDeRhamSources.originalUnit p K B X PX SX)).mapIso (eqToIso hm)

/-- Relative cotangent projection is the original native inverse image of the etale map. -/
def rho : omA (p := p) (K := K) (B := B) (X := X) (PX := PX) (SX := SX) (H := H) ⟶
    omR (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) :=
  (modulePullback (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
    SX.regular (ProEtaleDeRhamSources.originalUnit p K B X PX SX)).map H.relativeProjection

/-- Original K scalar compatibility fixes the absolute source ring before the cofactor. -/
abbrev ScalarCompatibility := axX (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H) ≫
    etaX (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) =
  AnalyticAbsoluteDeRhamSources.proKScalar p K B X PX SX H.scalarX

variable (hK : ScalarCompatibility (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
  (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H))

/-- Absolute term isos use the native original coefficient iso and literal scalar equality. -/
def absoluteTerms (n : ℕ) : H.absoluteCochains.native.obj.X (n : ℤ) ≅
    (restrict (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) SX.regular
      ((ax (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
        (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)) ≫
      ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
    (tensor SX.regular (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M))
      (exterior SX.regular (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX) n)) :=
  H.absoluteCochains.terms n ≪≫
    (restrict (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) SX.regular
      (AnalyticAbsoluteDeRhamSources.proKScalar p K B X PX SX H.scalarX)).mapIso
        ((tensorFunctor SX.regular (exterior SX.regular (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX) n)).mapIso
          (absoluteCoefficientIso (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
            (PX := PX) (PY := PY) (SX := SX) (SY := SY) (Ω := Ω) (M := M) (H := H)).symm) ≪≫
    eqToIso (by rw [hK])

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

abbrev BaseCotangentType :=
  (pullback Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)).obj
      (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) ⟶
  (restrict (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) SX.regular
    (ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N)).obj
      (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX)

abbrev CofactorType := MathlibExt.CategoryTheory.NativeGaussManinOutputs.CofactorSource
  Q.functor SY.regular (AnalyticAbsoluteDeRhamSources.constantK p K B X PX)
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (ax (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H))
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)
    (nativeRelative (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f)
      (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D))

variable (beta : BaseCotangentType (E := E) (Q := Q) (N := N) (H := H))

abbrev CotangentNormalization := GaussManinCofactorNormalization.IsCotangentSource
  (G := Q.functor) (SY := SY.regular) (SX := (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)) (OX := SX.regular) (η := (ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N))
  (s := (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)) (ΩY := (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)) (ΩA := (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX)) (ΩR := (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)))
  (β := beta) (ρ := rho (H := H)) H.formSourceY.differential H.formSourceX.differential FS.differential

abbrev TwoBaseWedgeType := GaussManinCofactorNormalization.BaseTwoWedgeSource
  Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) SX.regular (ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M)) (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX) beta

variable (W : TwoBaseWedgeType (E := E) (Q := Q) (N := N) (H := H) (beta := beta))
  (CB : CofactorType (E := E) (Q := Q) (N := N) (D := D) (H := H))

abbrev CofactorQualification := GaussManinCofactorNormalization.Qualification
  (G := Q.functor) (SY := SY.regular) (KX := (AnalyticAbsoluteDeRhamSources.constantK p K B X PX)) (SX := (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)) (OX := SX.regular)
  (ax := (ax (E := E) (Q := Q) (H := H))) (η := (ProEtaleDeRhamSources.relativeScalar p K B X Y f PX PY SX SY E Q N)) (s := (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)) (ΩY := (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)) (F := (nativeRelative (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (D := D)))
  (M := (ProEtaleDeRhamSources.coefficient (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω) (M := M))) (ΩA := (AnalyticAbsoluteDeRhamSources.forms p K B X PX SX H.absoluteFormsX)) (ΩR := (ProEtaleDeRhamSources.forms (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (SX := SX) (Ω := Ω)))
  (absolute := H.absoluteCochains.native)
  (absoluteTerms := absoluteTerms (E := E) (Q := Q) (N := N) (H := H) (hK := hK))
  (relativeTerms := DS.terms) (β := beta) (ρ := rho (H := H)) W CB

abbrev QualifiedCofactorType :=
  Σ B : CofactorType (E := E) (Q := Q) (N := N) (D := D) (H := H),
    CofactorQualification (E := E) (Q := Q) (N := N) (D := D) (DS := DS)
      (H := H) (hK := hK) (beta := beta) (W := W) (CB := B)

variable [(NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY)).Additive]
  [PreservesFiniteLimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteColimits (NativeRestrictionCohomologyMaps.restrictY (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY))]
  [PreservesFiniteLimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]
  [PreservesFiniteColimits (NativeTensorProjectionMaps.tensorY SY.regular (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]
  [ExactCochainUnit (NativeRestrictionCohomologyMaps.restrictX (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (ax (E := E) (Q := Q) (H := H)))]
  [ExactCochainUnit (NativeTensorProjectionMaps.tensorX Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY))]

abbrev RestrictionSquareType := NativeRestrictionCohomologyMaps.SourceSquare
  Q.functor (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (ax (E := E) (Q := Q) (H := H)) (constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K)) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
abbrev TensorSquareType := NativeTensorProjectionMaps.SourceSquare Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY)

variable (RS : RestrictionSquareType (E := E) (Q := Q) (H := H))
  (NS : TensorSquareType (E := E) (Q := Q) (H := H))
  (AO : DerivedAdjunctionSource Q.functor SY.regular (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular))

/-- The constructed native tensor, scalar-restriction and cochain-shift target map. -/
def gaussManinTarget (i : ℤ) := NativeGaussManinOutputs.targetMap
  Q.functor (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (ax (E := E) (Q := Q) (H := H)) (constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K)) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (nativeRelative (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (D := D)) RS NS AO i

/-- The OUTPUT higher connection is the ORIGINAL native cochain boundary transported by
the separately proved finite-form projection. -/
def higherConnection (i : ℤ) [IsIso (gaussManinTarget
    (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
    (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX)
    (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D)
    (H := H) (RS := RS) (NS := NS) (AO := AO) i)] :=
  letI : IsIso (NativeGaussManinOutputs.targetMap
  Q.functor (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (ax (E := E) (Q := Q) (H := H)) (constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K)) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular) (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (nativeRelative (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (D := D)) RS NS AO i) := by
    change IsIso (gaussManinTarget
      (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY)
      (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX)
      (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D)
      (H := H) (RS := RS) (NS := NS) (AO := AO) i)
    infer_instance
  NativeGaussManinOutputs.connectionMap Q.functor (AnalyticAbsoluteDeRhamSources.constantK p K B Y PY) SY.regular (AnalyticAbsoluteDeRhamSources.constantK p K B X PX) (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q) (AnalyticAbsoluteDeRhamSources.proKScalar p K B Y PY SY H.scalarY) (ax (E := E) (Q := Q) (H := H)) (constantPush (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor (BaseField.carrier p K)) (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
    (AnalyticAbsoluteDeRhamSources.forms p K B Y PY SY H.absoluteFormsY) (nativeRelative (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (D := D)) CB RS NS AO i

abbrev BaseOneFormType := AnalyticAbsoluteDeRhamSources.OneFormSource
  p K B Y PY SY H.absoluteFormsY H.scalarY H.formSourceY

/-- The actual original cofactor and intermediate finite-form projection source. This factory
contains no higher vector bundle, connection or period comparison oracle. -/
structure GaussManinFactory where
  scalar : ScalarCompatibility (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H)
  cotangent : BaseCotangentType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H)
  cotangent_source : CotangentNormalization (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (FS := FS) (H := H) (beta := cotangent)
  wedge : TwoBaseWedgeType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (H := H) (beta := cotangent)
  cofactor : CofactorType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (H := H)
  cofactor_source : CofactorQualification (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (DS := DS)
    (H := H) (hK := scalar) (beta := cotangent) (W := wedge) (CB := cofactor)
  restriction : RestrictionSquareType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)
  tensor : TensorSquareType (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (H := H)
  adjunction : DerivedAdjunctionSource Q.functor SY.regular
    (ProEtaleDeRhamSources.relativeRing p K B X Y f PX PY SY E Q)
    (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor SY.regular)
  projection : ∀ i : ℤ, IsIso (gaussManinTarget (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (RS := restriction) (NS := tensor) (AO := adjunction) i)

def GaussManinFactory.connection (S : GaussManinFactory (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (Ω := Ω) (M := M) (D := D) (DS := DS) (FS := FS) (H := H)) (i : ℤ) :=
  letI : IsIso (gaussManinTarget (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (RS := S.restriction) (NS := S.tensor) (AO := S.adjunction) i) := S.projection i
  higherConnection (p := p) (K := K) (B := B) (X := X) (Y := Y) (f := f) (PX := PX) (PY := PY) (SX := SX) (SY := SY) (E := E) (Q := Q) (N := N) (FX := FX) (IX := IX) (T := T) (TQ := TQ) (L := L) (Ω := Ω) (M := M) (D := D) (H := H) (CB := S.cofactor) (RS := S.restriction) (NS := S.tensor) (AO := S.adjunction) i

end MathlibExt.AlgebraicGeometry.RelativeGaussManinSources
