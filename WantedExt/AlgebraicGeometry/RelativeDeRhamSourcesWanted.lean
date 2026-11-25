/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativePadicPeriodComparisons
public import MathlibExt.AlgebraicGeometry.ProEtaleIntegralTowers

/-!
# Direct source requests for actual proper smooth relative de Rham geometry

All geometry and coefficients are the actual analytic/formal pro-site
objects over the original general complete discretely valued K/Q_p.
These are construction/source requests, independent of provider proof
availability. Base associated coefficients are INPUT; higher bundles,
filtrations, Gauss--Manin and comparisons are OUTPUT requests elsewhere.

Sources: Scholze, arXiv:1205.3463v2, Definitions 6.8, 7.4--7.5 and
Theorem 8.8; BMS arXiv:1602.03148v3 Section 5.1; completed Atlas PR2245
`76de3f2665f9c44b06932f9861ee9aae65e04395`, Apache 2.0 source port.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeDeRhamSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPeriodPullbackSources
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

public def_wanted etaleBaseChange (h : RelativeScope p B X Y f) : EtaleBaseChangeSource p f.left

public def_wanted fullProBaseChange (h : RelativeScope p B X Y f) : ProBaseChangeSource p f.left E

public theorem_wanted fullProContinuous (h : RelativeScope p B X Y f) :
  Q.functor.IsContinuous (proTopology p Y.left PY) (proTopology p X.left PX)

/-- Every original ring unit and every full-pro presentation is retained by this source square. -/
public def_wanted originalRingInverseSquare (h : RelativeScope p B X Y f) :
  RingSquare (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left)

public def_wanted fullProPointProjection (h : RelativeScope p B X Y f) :
  PointProjectionSource p K B X Y f PX PY E Q N

public theorem_wanted originalPositivePreservation (h : RelativeScope p B X Y f) :
  PositivePreservation p K B X Y f PX PY SX SY E

public def_wanted naturalPeriodMaps (h : RelativeScope p B X Y f)
    (hp : PositivePreservation p K B X Y f PX PY SX SY E) :
  NaturalPeriodMaps p K B X Y f PX PY SX SY E Q N hp

/-- Actual continuous quotient forms on all original affinoid etale charts. -/
public def_wanted relativeDifferentials (h : RelativeScope p B X Y f) :
  AnalyticRelativeDeRhamSources.DifferentialSource p f.left SX.regularSheaf

public def_wanted absoluteDifferentials (h : RelativeScope p B X Y f) :
  AnalyticRelativeDeRhamSources.DifferentialSource p X.hom SX.regularSheaf

public def_wanted relativeFromAbsolute (h : RelativeScope p B X Y f)
    (ΩA : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom SX.regularSheaf)
    (ΩR : AnalyticRelativeDeRhamSources.DifferentialSource p f.left SX.regularSheaf)
    (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p X.hom SX.regularSheaf ΩA)
    (ρ : ΩA.oneForms ⟶ ΩR.oneForms)
    (hρ : ∀ U a, (ρ.val.app U).hom (ΩA.differential U a) = ΩR.differential U a) :
  AnalyticRelativeDeRhamSources.RelativeCoefficientInputSource
    (p := p) (B := B) (Z := X) (hZ := SX.regularSheaf) (g := f.left)
    (ΩA := ΩA) (ΩR := ΩR) (M := M) (ρ := ρ)

variable (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p f.left SX.regularSheaf)
  (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p f.left SX.regularSheaf Ω)

public theorem_wanted locallyFiniteRelativeForms (h : RelativeScope p B X Y f) :
  MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs.LocallyFiniteForms Ω.oneForms

/-- Actual coefficient cochains, original image filtration and public native extended connection. -/
public def_wanted filteredEtaleDeRhamSource (h : RelativeScope p B X Y f) :
  AnalyticRelativeDeRhamSources.FilteredDeRhamSource p f.left E SX.regularSheaf SY.regularSheaf Ω M

variable [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left SX.regularSheaf)
  SX.regular (ProEtaleDeRhamSources.originalUnit p K B X PX SX)).IsRightAdjoint]

public def_wanted relativeProFormSource (h : RelativeScope p B X Y f) :
  ProEtaleDeRhamSources.FormSource p K B X Y f PX SX Ω

variable (D : AnalyticRelativeDeRhamSources.FilteredDeRhamSource p f.left E SX.regularSheaf SY.regularSheaf Ω M)
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

public theorem_wanted cochainInverseImageMono (h : RelativeScope p B X Y f) :
  (cochainTransfer (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
      (regularEtale p Y.left SY.regularSheaf)).PreservesMonomorphisms

variable [(cochainTransfer (J₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p Y.left)
    (T₁ := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
    (J₂ := proTopology p Y.left PY) (T₂ := proTopology p X.left PX)
    E.functor Q.functor (etaleInclusion p Y.left) (etaleInclusion p X.left) N
      (regularEtale p Y.left SY.regularSheaf)).PreservesMonomorphisms]

/-- The output identifies every pro cochain on original inverse-image/tensor/exterior units. -/
public def_wanted proDeRhamSource (h : RelativeScope p B X Y f) :
  ProEtaleDeRhamSources.Source p K B X Y f PX PY SX SY E Q N Ω M D

variable (FS : ProEtaleDeRhamSources.FormSource p K B X Y f PX SX Ω)
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.regular SX.naiveStructuralPositive
    SX.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) SX.naiveStructuralPositive SX.naiveStructuralFull
    SX.scalars.positiveToFull).IsRightAdjoint]

public def_wanted positiveRelativePeriodConnection (h : RelativeScope p B X Y f) :
  PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential

public def_wanted fullRelativePeriodConnection (h : RelativeScope p B X Y f)
    (P : PositiveConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
      (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential) :
  FullConnectionSource p K SX.regular SX.positive SX.untilting SX.scalars
    (ProEtaleDeRhamSources.forms p K B X Y f PX SX Ω) FS.differential P

end WantedExt.AlgebraicGeometry.RelativeDeRhamSources
