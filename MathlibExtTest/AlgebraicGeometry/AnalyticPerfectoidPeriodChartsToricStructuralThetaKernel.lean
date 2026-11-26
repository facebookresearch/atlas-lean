/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodChartsToricStructuralThetaKernel

/-!
# Multiples of toric coordinates in the structural theta kernel

Every section times a toric infinitesimal coordinate has zero structural theta image.

Sources: Scholze, *p-adic Hodge theory for rigid-analytic varieties*, arXiv:1205.3463v2,
Theorem 6.5, Definition 6.8 and Proposition 6.10; Bhatt--Morrow--Scholze, *Integral p-adic
Hodge theory*, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.AnalyticPerfectoidPeriodChartsToricStructuralThetaKernel

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources
open AnalyticPerfectoidPeriodCharts
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources


example
    (p : ℕ) [Fact p.Prime] (K : BaseField p) (B : BaseRealization p K)
    (X : Over B.analytic) (P : AnalyticProObjectSites.PointRealization p X.left)
    [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) CommRingCat.{1}]
    [HasSheafify (proTopology p X.left P) CommRingCat.{1}]
    [(etaleInclusion p X.left).IsContinuous
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (proTopology p X.left P)]
    [((etaleInclusion p X.left).sheafPushforwardContinuous CommRingCat.{1}
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left)
      (proTopology p X.left P)).IsRightAdjoint]
    [IsIso (constantInverseMap
      (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
      (etaleInclusion p X.left) (WittVector p (BaseField.residueField p K)))]
    [HasSheafify (AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) AddCommGrpCat.{1}]
    [(AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left).WEqualsLocallyBijective
      AddCommGrpCat.{1}]
    [HasSheafify (proTopology p X.left P) AddCommGrpCat.{1}]
    [(proTopology p X.left P).WEqualsLocallyBijective AddCommGrpCat.{1}]
    (S : Source p K B X P)
    (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom S.regularSheaf)
    [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
      S.regular (originalRingUnit p K B X P S)).IsRightAdjoint]
    (AΩ : AbsoluteFormSource p K B X P S Ω)
    (C : ToricChart p K B X P S (absoluteForms p K B X P S Ω) AΩ.differential)
    (i : Fin C.dimension)
    (a : S.scalars.naiveStructuralInf.obj.obj (op C.boundary.formal)) :
    ((S.scalars.structuralTheta.hom.app (op C.boundary.formal)).hom)
      (a * ToricChart.infCoordinate p K B X P S (absoluteForms p K B X P S Ω)
        AΩ.differential C i) = 0 := by
  rw [map_mul,
    WantedExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts.toricStructuralThetaKernel,
    mul_zero]

end MathlibExtTest.AlgebraicGeometry.AnalyticPerfectoidPeriodChartsToricStructuralThetaKernel
