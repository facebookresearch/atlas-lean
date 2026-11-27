/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison

/-!
# Exactness requests for the relative integral period comparison

The comparison of integral relative Theorem 8.8(i) (`RelativeIntegralPeriodComparison.comparison`)
also uses the derived pullback of `B_dR⁺`-modules along the relative map, whose exactness (a
flatness of `B_dR⁺` on `X` over the inverse image of `B_dR⁺` on `Y`) is not established; the
comparison isomorphism and its scalar square are therefore not requested here, so as not to make a
request conditional on a hypothesis that may fail. What is requested are the exactness statements
that do hold: the scalar extension of `Ẑ_p`-modules, and the module inverse image along the unit to
an inverse-image ring (the sheaf inverse image), with their normalized derived adjunctions. They
discharge the corresponding hypotheses of the Gauss–Manin and higher-association requests.

The higher-lisse guard (`RelativeIntegralPeriodComparison.HigherLisseAt`) is that ACTUAL native
R^i f_* L is lisse in the sense of `ProEtaleIntegralLisseModules.IsLisse`, locally a finite
`ℤ_p`-module (torsion allowed, as in Scholze's Definition 8.1), not that it is finite locally
free.

Source: Scholze, arXiv:1205.3463v2, Definitions 8.1--8.3 and Theorem 8.8.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeIntegralPeriodComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
open AnalyticCoefficientPeriodScalars MathlibExt.AlgebraicGeometry.RelativeIntegralPeriodComparison
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedComplexInverseImageSources
open MathlibExt.CategoryTheory.NativeScalarProjectionMaps

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

/-- The scalar extension of `Ẑ_p`-modules along the relative pro-étale map is exact: `Ẑ_p` on `X`
is the inverse image of `Ẑ_p` on `Y`, so the derived pullback is computed termwise. -/
public def_wanted coefficientPullbackExact (h : RelativeScope p B X Y f) :
    PullbackSourceUnit Q.functor (Zhat p Y.left PY) (Zhat p X.left PX)
      (coefficientScalar p K B X Y f PX PY E Q N PS)

/-- The normalized derived adjunction of `Ẑ_p`-modules along the relative pro-étale map. -/
public def_wanted coefficientDerivedAdjunction (h : RelativeScope p B X Y f)
    [PullbackSourceUnit Q.functor (Zhat p Y.left PY) (Zhat p X.left PX)
      (coefficientScalar p K B X Y f PX PY E Q N PS)] :
    DerivedAdjunctionSource Q.functor (Zhat p Y.left PY) (Zhat p X.left PX)
      (coefficientScalar p K B X Y f PX PY E Q N PS)

/-- For a proper smooth morphism $f : X \to Y$ of smooth, locally Noetherian analytic spaces over
the base realization $B$ of $K$ (`RelativeScope`) and a sheaf of rings $S$ on the pro-étale site
of $Y$, with enough injective modules over $S$ and over $f^{-1} S$ and with a left adjoint (the
module pullback) to the module pushforward along the unit $S \to f_* f^{-1} S$: the module
pullback along this unit is exact on bounded-below complexes, that is, the unit of its right
derived functor is an isomorphism at every bounded-below complex of $S$-modules
(`PullbackSourceUnit`). This pullback is the sheaf inverse image $f^{-1}$. -/
public def_wanted inverseUnitPullbackExact (h : RelativeScope p B X Y f)
    (S : Sheaf (proTopology p Y.left PY) CommRingCat.{1}) [EnoughInjectives (Modules S)]
    [EnoughInjectives (Modules (inverseRing (J := proTopology p Y.left PY)
      (T := proTopology p X.left PX) Q.functor S))]
    [(pushforward Q.functor S (inverseRing (J := proTopology p Y.left PY)
      (T := proTopology p X.left PX) Q.functor S)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)).IsRightAdjoint] :
    PullbackSourceUnit Q.functor S
      (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)

/-- The normalized derived adjunction along the unit to an inverse-image ring. -/
public def_wanted inverseUnitDerivedAdjunction (h : RelativeScope p B X Y f)
    (S : Sheaf (proTopology p Y.left PY) CommRingCat.{1}) [EnoughInjectives (Modules S)]
    [EnoughInjectives (Modules (inverseRing (J := proTopology p Y.left PY)
      (T := proTopology p X.left PX) Q.functor S))]
    [(pushforward Q.functor S (inverseRing (J := proTopology p Y.left PY)
      (T := proTopology p X.left PX) Q.functor S)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)).IsRightAdjoint]
    [PullbackSourceUnit Q.functor S
      (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)] :
    DerivedAdjunctionSource Q.functor S
      (inverseRing (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)
      (inverseUnit (J := proTopology p Y.left PY) (T := proTopology p X.left PX) Q.functor S)

end WantedExt.AlgebraicGeometry.RelativeIntegralPeriodComparison
