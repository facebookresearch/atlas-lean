/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources

/-!
# Direct original absolute de Rham source requests

All objects are the original native analytic/pro-site inverse images.
Every connection, form differential and degree extension is normalized
by the actual continuous affinoid quotient and public native Stacks
connection. These are BASE source constructions; no higher vector
bundle or higher comparison is supplied.

Sources: Scholze, arXiv:1205.3463v2, Definitions 6.8 and 7.4--7.5,
Proposition 8.5 and Theorem 8.8; complete PR2245 native de Rham port,
`76de3f2665f9c44b06932f9861ee9aae65e04395`, Apache 2.0.
-/
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProperSmoothSources GeneralPadicCoefficientFields
open QualifiedStructuralPeriodSites AnalyticProEtaleCoefficientSources
open MathlibExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.NativeConnectionProperties
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
  [(modulePushforward (etaleInclusion p X.left) (regularEtale p X.left S.regularSheaf)
    S.regular (AnalyticPerfectoidPeriodCharts.originalRingUnit p K B X P S)).IsRightAdjoint]


public def_wanted originalEtaleKScalar (hSmooth : IsSmooth p X.hom) : EtaleKScalarSource p K B X P S

variable [IsIso (constantInverseMap
  (J := AnalyticDiamondEtaleSites.analyticEtaleTopology p X.left) (T := proTopology p X.left P)
  (etaleInclusion p X.left) (BaseField.carrier p K))]
  (k : EtaleKScalarSource p K B X P S)
  (Ω : AnalyticRelativeDeRhamSources.DifferentialSource p X.hom S.regularSheaf)
  (AΩ : AnalyticPerfectoidPeriodCharts.AbsoluteFormSource p K B X P S Ω)

public def_wanted originalOneFormDifferential (hSmooth : IsSmooth p X.hom) :
  OneFormSource p K B X P S Ω k AΩ

variable (M : AnalyticRelativeDeRhamSources.BaseCoefficientInput p X.hom S.regularSheaf Ω)

public def_wanted originalCoefficientFiltration (hSmooth : IsSmooth p X.hom) :
  FiltrationSource p K B X P S Ω M

public def_wanted absoluteCoefficientCochains (hSmooth : IsSmooth p X.hom) :
  AbsoluteComplexSource p K B X P S Ω M k

variable (A : AbsoluteComplexSource p K B X P S Ω M k)

public theorem_wanted absoluteCoefficientConnectionLeibniz (hSmooth : IsSmooth p X.hom) :
  IsConnection (constantK p K B X P) S.regular (proKScalar p K B X P S k)
    (coefficient p K B X P S Ω M) (forms p K B X P S Ω) AΩ.differential A.connectionMap

variable (D₁ : OneFormSource p K B X P S Ω k AΩ)
  (W : WedgeSource S.regular (coefficient p K B X P S Ω M) (forms p K B X P S Ω))
  (N : ExtensionSource (constantK p K B X P) S.regular (proKScalar p K B X P S k)
    (coefficient p K B X P S Ω M) (forms p K B X P S Ω) A.connectionMap D₁.native.sections W)

public theorem_wanted absoluteCoefficientIntegrable (hSmooth : IsSmooth p X.hom) :
  IsIntegrable (constantK p K B X P) S.regular (proKScalar p K B X P S k)
    (coefficient p K B X P S Ω M) (forms p K B X P S Ω) A.connectionMap D₁.native.sections W N

variable (F : FiltrationSource p K B X P S Ω M)

public theorem_wanted absoluteCoefficientGriffiths (hSmooth : IsSmooth p X.hom) :
  Griffiths (constantK p K B X P) S.regular (proKScalar p K B X P S k)
    (coefficient p K B X P S Ω M) (forms p K B X P S Ω) A.connectionMap F.filtration

end WantedExt.AlgebraicGeometry.AnalyticAbsoluteDeRhamSources
