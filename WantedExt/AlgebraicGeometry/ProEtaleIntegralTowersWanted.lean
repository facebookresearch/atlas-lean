/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProEtaleIntegralTowers

/-!
# Direct integral finite-image realization source requests

All units, finite projections, the whole-diagram injective resolution
and the Milnor fibre are the original native constructions. The output
Zhat action is fixed at EVERY finite projection by locally constant
reductions of actual continuous functions. Finitely generated torsion
coefficients remain allowed. No global rational lattice is requested.

Sources: Scholze, arXiv:1205.3463v2, Definitions 8.1--8.3 and
Proposition 8.2; BMS arXiv:1602.03148v3, Section 5.1.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ProEtaleIntegralTowers

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticProObjectSites AnalyticProEtaleCoefficientSources
open MathlibExt.AlgebraicGeometry.ProEtaleIntegralTowers
open MathlibExt.CategoryTheory.ResolvedFiniteInverseImages

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (X : AnalyticAdicSpace p)
  (hX : IsLocallyNoetherian p X) (P : PointRealization p X)
  [∀ U : AnalyticProObjectSites.Etale p X,
    (Over.forget U).IsContinuous ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U)
      (AnalyticDiamondEtaleSites.analyticEtaleTopology p X)]
  [∀ U : AnalyticProObjectSites.Etale p X,
    HasSheafify ((AnalyticDiamondEtaleSites.analyticEtaleTopology p X).over U) (ModuleCat.{1} ℤ_[p])]
  [(etaleEmbedding p X).IsContinuous
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)]
  [((etaleEmbedding p X).sheafPushforwardContinuous (ModuleCat.{1} ℤ_[p])
    (AnalyticDiamondEtaleSites.analyticEtaleTopology p X) (proTopology p X P)).IsRightAdjoint]
  [Abelian (ProCoefficients p X P)] [EnoughInjectives (ℕᵒᵖ ⥤ ProCoefficients p X P)]
  [HasLimitsOfShape (Discrete ℕ) (ProCoefficients p X P)] (T : LisseIntegralTower p X)

include hX

public def_wanted nativeFiniteResolutionQualification (hNoeth : IsLocallyNoetherian p X) :
  Qualification (finiteInverseImage p X P) T.tower

variable [HasSheafify (proTopology p X P) CommRingCat.{1}]
  (Q : Qualification (finiteInverseImage p X P) T.tower)

public def_wanted integralRealization (hNoeth : IsLocallyNoetherian p X) : IntegralRealizationSource p X P T Q

/-- **Pro-étale derived limit of a lisse tower is concentrated in degree 0.** Let $p$ be a prime,
$X$ a locally Noetherian analytic adic space (`AnalyticAdicSpace p`) with a chosen point
realization `P` defining its pro-étale site, and `T` a lisse integral tower on $X$: finite locally
constant étale sheaves $T_n$ of $\mathbb{Z}_p$-modules killed by $p^{n+1}$, pro-isomorphic to a
tower $T'$ in which each transition map $T'_{n+1} \to T'_n$ is a cokernel of multiplication by
$p^{n+1}$. Assume that the terms of the injective resolution of the tower of pullbacks
$\nu^* T_n$ to the pro-étale site, and their product, are K-injective (`Q`). Then the derived
inverse limit of the $\nu^* T_n$ (`derivedRealization`) has zero cohomology sheaves in every
degree $i \ne 0$. It assumes the site-theoretic properties that its typeclass arguments assert:
continuity of the comparison functors between the étale and pro-étale sites, existence of
sheafification, and an abelian category of pro-étale sheaves with enough injective towers and
countable products. -/
public theorem_wanted derivedIntegralRealizationConcentrated (hNoeth : IsLocallyNoetherian p X) (i : ℤ) (hi : i ≠ 0) :
  IsZero ((DerivedCategory.homologyFunctor (ProCoefficients p X P) i).obj
    (derivedRealization p X P T Q))

end WantedExt.AlgebraicGeometry.ProEtaleIntegralTowers
