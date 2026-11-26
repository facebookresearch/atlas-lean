/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts
public import MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodChartsToricStructuralThetaKernel

/-!
# Direct qualified affinoid-perfectoid period chart requests

The forms are the ACTUAL absolute Omega_X/K continuous quotient sheaf,
followed by its ORIGINAL native pro inverse image. Toric coordinate
qualification retains an actual finite original affinoid stage, native
K scalars and a finite etale rational polydisc map. Taylor is fixed on
every finite structural theta quotient. The full connection is the
local ABSOLUTE-theta-generator fraction extension of the positive one.
The toric coordinates lie in the structural theta kernel
(`toricStructuralThetaKernel`, in
`MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodChartsToricStructuralThetaKernel`).

The structural period objects are the naive ones of `StructuralDeRhamPeriodSources` (Scholze's
withdrawn Definition 6.8, erratum item (3)): the Taylor map is requested, but its invertibility
(Proposition 6.10) is not, since it fails for them; it awaits the corrected finite-stage
construction.

Sources: Scholze, arXiv:1205.3463v2, Theorem 6.5, Definition 6.8 and
Proposition 6.10; BMS arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources AnalyticPerfectoidPeriodCharts
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources

variable (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
  (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
  [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
  [(etaleInclusion p X.left).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
  [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)).IsRightAdjoint]
  [IsIso (constantInverseMap
    (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
    (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
  [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
  [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  [HasSheafify (proTopology p X.left P) AddCommGrpCat.{1}]
  [(proTopology p X.left P).WEqualsLocallyBijective AddCommGrpCat.{1}]
  (S : Source p K B X P)
  (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom S.regularSheaf)
  [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (originalRingUnit p K B X P S)).IsRightAdjoint]

public def_wanted absoluteProFormSource (hSmooth : IsSmooth p X.hom) :
  AbsoluteFormSource p K B X P S Ω

variable (AΩ : AbsoluteFormSource p K B X P S Ω)

public theorem_wanted affinePerfectoidToricCover (hSmooth : IsSmooth p X.hom) :
  HasToricCover p K B X P S (absoluteForms p K B X P S Ω) AΩ.differential

variable (C : ToricChart p K B X P S (absoluteForms p K B X P S Ω) AΩ.differential)

variable [∀ U : AnalyticProObjectSites.ProEtaleSite p X.left,
  HasSheafify ((proTopology p X.left P).over U) CommRingCat.{1}]

public def_wanted toricTaylorSource
    (hC : ToricChart.CoordinateSource p K B X P S (absoluteForms p K B X P S Ω) AΩ.differential C) :
  TaylorSource p K B X P S (absoluteForms p K B X P S Ω) AΩ.differential C

variable [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) S.regular S.naiveStructuralPositive
    S.scalars.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 (AnalyticProObjectSites.ProEtaleSite p X.left)) S.naiveStructuralPositive S.naiveStructuralFull
    S.scalars.positiveToFull).IsRightAdjoint]

public def_wanted positiveAbsolutePeriodConnection (hSmooth : IsSmooth p X.hom) :
  PositiveConnectionSource p K S.regular S.positive S.untilting S.scalars
    (absoluteForms p K B X P S Ω) AΩ.differential

public def_wanted fullAbsolutePeriodConnection (hSmooth : IsSmooth p X.hom)
    (PC : PositiveConnectionSource p K S.regular S.positive S.untilting S.scalars
      (absoluteForms p K B X P S Ω) AΩ.differential) :
  FullConnectionSource p K S.regular S.positive S.untilting S.scalars
    (absoluteForms p K B X P S Ω) AΩ.differential PC

end WantedExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts
