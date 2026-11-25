/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SyntomicNearbyComparisons

/-!
# Source-defined finite and integral syntomic/nearby comparison requests

The completed definitions specify the original O_C coefficients, all
affine formal opens and chart arrows, actual syntomic fibers, coefficient
cones/maps, native full pro-objects, finite signed Tate roots/tensors/duals,
right-derived nearby pushforward and canonical truncation functors.

Source construction and theorem endpoints are separate. The finite
equivalences are output with their full modulus square. No equivalent
target, comparison isomorphism or inverse-limit theorem is an input.

References: BMS19 arXiv:1802.03261v2, Section 7.4, Theorem 10.1,
Remarks 10.3/10.4 and Theorem 1.15(2); BMS18 arXiv:1602.03148v3,
Section 5.1; Scholze arXiv:1205.3463v2, Definitions 3.1/3.9.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SyntomicNearbyComparisons

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FormalGenericFibreModels FormalNearbyCycleModels FormalSyntomicSiteModels
open PrismaticSyntomicModels AbsolutePrismaticBasis PrismaticFilteredTwists
open FiniteTateCoefficientTowers AnalyticTateAdicModels AnalyticDiamondEtaleSites
open SyntomicNearbyComparisons
open MathlibExt (FunctorialKInjective)

attribute [local instance] HasDerivedCategory.standard

public def_wanted actualIntegralBase (p : ℕ) [Fact p.Prime] (C : CompletePadicField p) : IntegralBase p C

public theorem_wanted qsynBasisContinuous (p : ℕ) [Fact p.Prime]
    (C : CompletePadicField p) (B : IntegralBase p C) :
    (basisInclusion p C B).IsContinuous (AbsolutePrismaticBasis.topology p B.ring)
      (QuasiSyntomicPrismSites.topology p B.ring)

variable (p : ℕ) [Fact p.Prime] (C : CompletePadicField p) (B : IntegralBase p C)
  [(basisInclusion p C B).IsContinuous (AbsolutePrismaticBasis.topology p B.ring)
    (QuasiSyntomicPrismSites.topology p B.ring)]
  (D : ∀ S : AbsolutePrismaticBasis.Basis p B.ring, InitialLift p (AbsolutePrismaticBasis.ring p S))
  (Z : ZeroReduction p B.ring D) (T : TwistTower p B.ring D Z)
  (F : FrobeniusModel p B.ring D Z T)

public def_wanted extendSyntomicFromBasis : QsynExtension p C B D Z T F

/-- Functorial K-injective resolutions on the quasisyntomic sheaves, used to derive the formal
restriction of syntomic cochains. -/
public def_wanted qsynKInjectiveResolution : FunctorialKInjective (QsynSheaves p C B)

public def_wanted restrictQsynToFormalEtale
    (X : FormalGenericFibreModels.FormalScheme p C)
    (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n)) : FormalRestriction p C B X

public def_wanted formalProObjectPoints
    (X : FormalGenericFibreModels.FormalScheme p C) : FormalProObjectSites.PointRealization p C X

public theorem_wanted formalEtaleProContinuous
    (X : FormalGenericFibreModels.FormalScheme p C) (P : FormalProObjectSites.PointRealization p C X) :
    (FormalProObjectSites.etaleEmbedding p C X).IsContinuous
      (formalEtaleTopology p C X) (FormalProObjectSites.topology p C X P)

public def_wanted genericProFibreExtension
    (X : FormalGenericFibreModels.FormalScheme p C) (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A) :
    FormalProObjectSites.GenericProModel p C E

public theorem_wanted genericProFibreContinuous
    (X : FormalGenericFibreModels.FormalScheme p C) (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A)
    (P : FormalProObjectSites.PointRealization p C X) (S : AnalyticProObjectSites.PointRealization p G)
    (H : FormalProObjectSites.GenericProModel p C E) :
    H.functor.IsContinuous (FormalProObjectSites.topology p C X P) (AnalyticProObjectSites.bmsTopology p G S)

public def_wanted formalProInverseImage
    (X : FormalGenericFibreModels.FormalScheme p C) (P : FormalProObjectSites.PointRealization p C X)
    [(FormalProObjectSites.etaleEmbedding p C X).IsContinuous
      (formalEtaleTopology p C X) (FormalProObjectSites.topology p C X P)] :
    SiteInverse (formalEtaleTopology p C X) (FormalProObjectSites.topology p C X P)
      (FormalProObjectSites.etaleEmbedding p C X)

public def_wanted analyticProInverseImage
    (G : AnalyticAdicSpace p) (h : AnalyticProObjectSites.IsLocallyNoetherian p G)
    (S : AnalyticProObjectSites.PointRealization p G)
    [(AnalyticProObjectSites.etaleEmbedding p G).IsContinuous
      (analyticEtaleTopology p G) (AnalyticProObjectSites.bmsTopology p G S)] :
    SiteInverse (analyticEtaleTopology p G) (AnalyticProObjectSites.bmsTopology p G S)
      (AnalyticProObjectSites.etaleEmbedding p G)

public def_wanted genericProDerivedNearby
    (X : FormalGenericFibreModels.FormalScheme p C)
    (G : AnalyticAdicSpace p) (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A)
    (P : FormalProObjectSites.PointRealization p C X) (S : AnalyticProObjectSites.PointRealization p G)
    (H : FormalProObjectSites.GenericProModel p C E)
    [H.functor.IsContinuous (FormalProObjectSites.topology p C X P) (AnalyticProObjectSites.bmsTopology p G S)] :
    H.HasDerivedNearby S (R := P)

public def_wanted canonicalGoodTruncationBridge (M : Type 2) [Category.{1} M] [Abelian M]
    [HasDerivedCategory M] : GoodTruncationBridge M

public def_wanted formalProKInjectiveResolution
    (X : FormalGenericFibreModels.FormalScheme p C) (P : FormalProObjectSites.PointRealization p C X) :
    FunctorialKInjective (FormalProObjectSites.Sheaves p C X P)

public def_wanted analyticProKInjectiveResolution
    (G : AnalyticAdicSpace p) (S : AnalyticProObjectSites.PointRealization p G) :
    FunctorialKInjective (FormalProObjectSites.GenericProModel.GenericSheaves S)

variable (X : FormalGenericFibreModels.FormalScheme p C)
  (hSmooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
  (G : AnalyticAdicSpace p) (hGeneric : AnalyticProObjectSites.IsLocallyNoetherian p G)
  (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A)
  [E.functor.IsContinuous (formalEtaleTopology p C X) (analyticEtaleTopology p G)]
  [E.HasDerivedNearby]
  (R : FormalRestriction p C B X)
  (RQ : FunctorialKInjective (QsynSheaves p C B))
  (K : TateTower p (analyticEtaleRings p G) (analyticEtaleTopology p G))

/-- Finite syntomic–nearby-cycle equivalences (Bhatt–Morrow–Scholze, *Topological Hochschild
homology and integral $p$-adic Hodge theory*, Theorem 10.1). Let $p$ be a prime, $C$ a complete
algebraically closed nonarchimedean extension of $\mathbb{Q}_p$, $X$ a $p$-adic formal scheme
over $\mathcal{O}_C$ all of whose reductions $X_n \to \operatorname{Spec}(\mathcal{O}_C/p^{n+1})$
are smooth, and $G$ a locally Noetherian analytic adic space that is the generic fibre of $X$
through the atlas `A` and the étale model `E`, whose nearby-cycle functor is assumed to have a
right derived functor $R\psi$. For the given integral base `B` of $\mathcal{O}_C$ with prismatic
data `D` and `Z`, formal restriction `R`, K-injective resolutions `RQ` of quasisyntomic sheaves
and Tate tower `K`, this constructs a twist tower `T`, a Frobenius model `F` and an extension `Q`
of the syntomic complexes from the basis, with isomorphisms, for all $i \in \mathbb{Z}$ and
$r \ge 0$, in the derived category of sheaves on the formal étale site of $X$, from the derived
restriction of the syntomic complex $\mathbb{Z}_p(i)$ modulo $p^{r+1}$ to
$\tau^{\le i} R\psi(\mathbb{Z}/p^{r+1}(i))$, compatible with the reduction maps from level
$r + 1$ to level $r$ (those of `K` on the target). It assumes that the site functors involved
are continuous. -/
public def_wanted finiteSyntomicNearbyEquivalences
    (smooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (genericNoetherian : AnalyticProObjectSites.IsLocallyNoetherian p G) :
    Σ T : TwistTower p B.ring D Z, Σ F : FrobeniusModel p B.ring D Z T,
      Σ Q : QsynExtension p C B D Z T F, FiniteEquivalences p C B D Z T F X G A E R Q RQ K

variable (P : FormalProObjectSites.PointRealization p C X) (S : AnalyticProObjectSites.PointRealization p G)
  [(FormalProObjectSites.etaleEmbedding p C X).IsContinuous
    (formalEtaleTopology p C X) (FormalProObjectSites.topology p C X P)]
  [(AnalyticProObjectSites.etaleEmbedding p G).IsContinuous
    (analyticEtaleTopology p G) (AnalyticProObjectSites.bmsTopology p G S)]
  (VP : SiteInverse (formalEtaleTopology p C X) (FormalProObjectSites.topology p C X P)
    (FormalProObjectSites.etaleEmbedding p C X))
  (VG : SiteInverse (analyticEtaleTopology p G) (AnalyticProObjectSites.bmsTopology p G S)
    (AnalyticProObjectSites.etaleEmbedding p G))
  (H : FormalProObjectSites.GenericProModel p C E)
  [H.functor.IsContinuous (FormalProObjectSites.topology p C X P) (AnalyticProObjectSites.bmsTopology p G S)]
  [H.HasDerivedNearby S (R := P)]
  (RP : FunctorialKInjective (FormalProObjectSites.Sheaves p C X P))
  (RG : FunctorialKInjective (FormalProObjectSites.GenericProModel.GenericSheaves S))

/-- Integral syntomic–nearby-cycle equivalence (Bhatt–Morrow–Scholze, *Topological Hochschild
homology and integral $p$-adic Hodge theory*, Theorem 10.1 and Remark 10.3). Let $p$ be a prime,
$C$ a complete algebraically closed nonarchimedean extension of $\mathbb{Q}_p$, $X$ a $p$-adic
formal scheme over $\mathcal{O}_C$ all of whose reductions
$X_n \to \operatorname{Spec}(\mathcal{O}_C/p^{n+1})$ are smooth, and $G$ a locally Noetherian
analytic adic space that is the generic fibre of $X$ through the atlas `A` and the étale model
`E`, whose nearby-cycle functor is assumed to have a right derived functor. Take the integral
base `B` of $\mathcal{O}_C$ with prismatic data `D` and `Z`, the formal restriction `R`,
K-injective resolutions `RQ` of quasisyntomic sheaves and the Tate tower `K`, and moreover point
realizations `P`, `S` defining the pro-étale sites of $X$ and $G$, inverse images `VP`, `VG` from
the étale to the pro-étale sites, the pro-étale extension `H` of the generic-fibre functor, whose
nearby-cycle functor is assumed to have a right derived functor $R\psi$, and K-injective
resolutions `RP`, `RG`. Then there are a twist tower `T`, a Frobenius model `F` and an extension
`Q` of the syntomic complexes from the basis with the following isomorphisms on the pro-étale site
of $X$ (`IntegralEquivalences`): for all $i \in \mathbb{Z}$ and $r \ge 0$, from the pullback of
the derived restriction of the syntomic complex $\mathbb{Z}_p(i)$ modulo $p^{r+1}$ to
$\tau^{\le i} R\psi$ of the pullback of $\mathbb{Z}/p^{r+1}(i)$, compatible with the reductions
from level $r + 1$ to level $r$; and for all $i$, from the derived limit over $r$ of the former to
$\tau^{\le i} R\psi$ of the derived limit of the pullbacks of the $\mathbb{Z}/p^{r+1}(i)$,
compatible with the projections to every level $r$. It assumes that the site functors involved
are continuous. -/
public theorem_wanted integralSyntomicNearbyEquivalence
    (smooth : ∀ n : ℕ, Smooth (X.structureMap.app n))
    (genericNoetherian : AnalyticProObjectSites.IsLocallyNoetherian p G) :
    ∃ (T : TwistTower p B.ring D Z) (F : FrobeniusModel p B.ring D Z T)
      (Q : QsynExtension p C B D Z T F),
      Nonempty (IntegralEquivalences p C B D Z T F X G A E R Q RQ K P S VP VG H RP RG)

end WantedExt.AlgebraicGeometry.SyntomicNearbyComparisons
