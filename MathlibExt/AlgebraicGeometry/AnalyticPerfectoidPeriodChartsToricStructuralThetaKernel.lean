/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts

/-!
# Toric coordinates in the structural theta kernel

The structural theta map annihilates the infinitesimal coordinates of toric charts.
The proof uses `UntiltingData.theta_teichmuller`: theta sends Teichmüller lifts to sharp.

Sources: Scholze, *p-adic Hodge theory for rigid-analytic varieties*, arXiv:1205.3463v2,
Theorem 6.5, Definition 6.8 and Proposition 6.10; Bhatt--Morrow--Scholze, *Integral p-adic
Hodge theory*, arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources
open AnalyticPerfectoidPeriodCharts
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.StructuralPeriodConnectionSources

open MathlibExt.CategoryTheory.SheafScalarQuotients
open MathlibExt.CategoryTheory.SheafKernelCompletion
open MathlibExt.CategoryTheory.SheafWittSource
open MathlibExt.CategoryTheory.UntiltingSheafSources

/-- **The toric coordinates lie in the kernel of the structural theta map.** Let $p$ be a prime,
$K$ a base field (`BaseField p`) with base realization $B$, $X$ an analytic space over $B$ with a
point realization $P$, $S$ a period source of $X$ (`Source`), $\Omega$ a differential source,
`AΩ` an absolute form source and $C$ a toric chart of the absolute forms with the differential of
`AΩ`. Assume that presheaves of commutative rings and of abelian groups on the étale and
pro-étale sites of $X$ have sheafifications, that sheafification of abelian-group presheaves
inverts exactly the locally bijective maps, that the inclusion of the étale site into the
pro-étale site is continuous with right-adjoint pushforwards of ring sheaves and of module
sheaves, and that the canonical map from the inverse image of the constant étale sheaf $W(k)$,
for $k$ the residue field of $K$, to the constant pro-étale sheaf $W(k)$ is an isomorphism. Then
for each coordinate index $i$ of $C$, the element $u_i = T_i - [T_i^\flat]$
(`ToricChart.infCoordinate`) of the naive structural ring $\mathcal{O}B_{\inf}$ at the boundary of
$C$, the difference of the chart's original coordinate $T_i$ and the Teichmüller lift of its tilt
root $T_i^\flat$, is sent to $0$ by the structural theta map
$\theta : \mathcal{O}B_{\inf} \to \widehat{\mathcal{O}}$. -/
public theorem toricStructuralThetaKernel
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
    (i : Fin C.dimension) :
  ((S.scalars.structuralTheta.hom.app (op C.boundary.formal)).hom)
    (ToricChart.infCoordinate p K B X P S (absoluteForms p K B X P S Ω)
      AΩ.differential C i) = 0 := by
  let U := op C.boundary.formal
  let t := stageCoordinate p K B X P S C.boundary C.stage (C.original i)
  let w := ((toSheafify (proTopology p X.left P) (wittPresheaf p (tilt p S.positive))).app
    U).hom (WittVector.teichmuller p (C.root i))
  change (S.scalars.structuralTheta.hom.app U).hom
    ((S.scalars.originalToInf.hom.app U).hom t -
      (S.scalars.absoluteToInf.hom.app U).hom
        ((localizePUnit p (inf p S.positive)).hom.app U w)) = 0
  rw [map_sub]
  have ho := congrArg (fun f => (f.hom.app U).hom t) S.scalars.original_theta
  have ha := congrArg (fun f => (f.hom.app U).hom
    ((localizePUnit p (inf p S.positive)).hom.app U w)) S.scalars.absolute_theta
  change (S.scalars.structuralTheta.hom.app U).hom ((S.scalars.originalToInf.hom.app U).hom t) =
    (S.scalars.originalTheta.hom.app U).hom t at ho
  change (S.scalars.structuralTheta.hom.app U).hom ((S.scalars.absoluteToInf.hom.app U).hom
    ((localizePUnit p (inf p S.positive)).hom.app U w)) =
      (S.untilting.rationalTheta.hom.app U).hom _ at ha
  rw [ho, ha]
  have hl : localizePUnit p (inf p S.positive) ≫ S.untilting.rationalTheta =
      S.untilting.theta ≫ localizePUnit p (positiveCompletion p S.positive) :=
    coprod.inl_desc _ _
  have ht := congrArg (fun f => (f.hom.app U).hom w) hl
  change (S.untilting.rationalTheta.hom.app U).hom
    ((localizePUnit p (inf p S.positive)).hom.app U w) =
      ((localizePUnit p (positiveCompletion p S.positive)).hom.app U).hom
        ((S.untilting.theta.hom.app U).hom w) at ht
  rw [ht]
  dsimp only [w]
  erw [UntiltingData.theta_teichmuller p S.positive S.untilting U (C.root i), C.sharp_source,
    sub_self]

end WantedExt.AlgebraicGeometry.AnalyticPerfectoidPeriodCharts
