/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalSyntomicSiteModels

/-!
# Finite and integral syntomic/nearby comparison targets

Finite equivalences are maps between the actual formal-étale syntomic
cone and the canonically truncated right-derived nearby object. Their
modulus square uses the actual p-power source cone map and the actual
signed Tate reduction on the target.

The integral source is the Milnor limit of the finite syntomic cochains
after pullback to the formal pro-étale site. The integral generic
coefficients use the same actual finite root/tensor/dual tower. The
integral nearby target uses the full formal-pro-object generic-fibre
extension, its fixed right-derived pushforward and native truncation.
No commutation of inverse image with an inverse limit is assumed.

References: BMS19 arXiv:1802.03261v2, Theorem 10.1, Remark 10.3,
Theorem 1.15(2); BMS18 arXiv:1602.03148v3, Section 5.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SyntomicNearbyComparisons

open CategoryTheory CategoryTheory.Limits Opposite
open FormalGenericFibreModels FormalNearbyCycleModels FormalSyntomicSiteModels
open PrismaticSyntomicModels AbsolutePrismaticBasis PrismaticFilteredTwists
open FiniteTateCoefficientTowers AnalyticTateAdicModels AnalyticDiamondEtaleSites

attribute [local instance] HasDerivedCategory.standard

universe v₁ v₂

/-- The inverse image is characterized as the left adjoint of the actual
site restriction, with the source morphism-of-sites exactness property. -/
structure SiteInverse {D E : Type 1} [Category.{v₁} D] [Category.{v₂} E]
    (J : GrothendieckTopology D) (K : GrothendieckTopology E) (f : D ⥤ E)
    [f.IsContinuous J K] where
  inverse : Sheaf J (ModuleCat.{1} ℤ) ⥤ Sheaf K (ModuleCat.{1} ℤ)
  adjunction : inverse ⊣ f.sheafPushforwardContinuous (ModuleCat.{1} ℤ) J K
  [additive : inverse.Additive]
  [finiteLimits : PreservesFiniteLimits inverse]

attribute [instance] SiteInverse.additive SiteInverse.finiteLimits

/-- Generic integration of the canonical derived truncation with native
cochain good truncation. Naturality and the inclusion into the original
cochain fix the comparison, including for all coefficient morphisms. -/
structure GoodTruncationBridge (M : Type 2) [Category.{1} M] [Abelian M]
    [HasDerivedCategory M] where
  iso : ∀ (K : CochainComplex M ℤ) (i : ℤ),
    (DerivedCategory.TStructure.t.truncLE i).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (K.truncLE i)
  inclusion : ∀ (K : CochainComplex M ℤ) (i : ℤ),
    (iso K i).hom ≫ DerivedCategory.Q.map (K.ιTruncLE i) =
      (DerivedCategory.TStructure.t.truncLEι i).app (DerivedCategory.Q.obj K)
  naturality : ∀ {K L : CochainComplex M ℤ} (f : K ⟶ L) (i : ℤ),
    (DerivedCategory.TStructure.t.truncLE i).map (DerivedCategory.Q.map f) ≫ (iso L i).hom =
      (iso K i).hom ≫ DerivedCategory.Q.map (CochainComplex.truncLEMap f i)

namespace GoodTruncationBridge

variable {M : Type 2} [Category.{1} M] [Abelian M] [HasDerivedCategory M]
  (B : GoodTruncationBridge M)

def preimageIso (Y : DerivedCategory M) (i : ℤ) :
    (DerivedCategory.TStructure.t.truncLE i).obj Y ≅
      DerivedCategory.Q.obj ((DerivedCategory.Q.objPreimage Y).truncLE i) :=
  (DerivedCategory.TStructure.t.truncLE i).mapIso (DerivedCategory.Q.objObjPreimageIso Y).symm ≪≫
    B.iso (DerivedCategory.Q.objPreimage Y) i

end GoodTruncationBridge

variable (p : ℕ) [Fact p.Prime] (C : CompletePadicField p) (B : IntegralBase p C)
  [(basisInclusion p C B).IsContinuous (AbsolutePrismaticBasis.topology p B.ring)
    (QuasiSyntomicPrismSites.topology p B.ring)]
  (D : ∀ S : AbsolutePrismaticBasis.Basis p B.ring, InitialLift p (AbsolutePrismaticBasis.ring p S))
  (Z : ZeroReduction p B.ring D) (T : TwistTower p B.ring D Z)
  (F : FrobeniusModel p B.ring D Z T)
  (X : FormalGenericFibreModels.FormalScheme p C) (G : AnalyticAdicSpace p)
  (A : GenericAtlas p C X G) (E : GenericEtaleModel p C A)
  [E.functor.IsContinuous (formalEtaleTopology p C X) (analyticEtaleTopology p G)]
  [E.HasDerivedNearby]
  (R : FormalRestriction p C B X) (Q : QsynExtension p C B D Z T F)
  (RQ : FunctorialKInjective (QsynSheaves p C B))
  (K : TateTower p (analyticEtaleRings p G) (analyticEtaleTopology p G))

def finiteTarget (i : ℤ) (r : ℕ) : DerivedCategory (FormalSheaves p C X) :=
  (DerivedCategory.TStructure.t.truncLE i).obj (E.finiteNearby (r + 1) i)

def targetReduction (i : ℤ) (r : ℕ) : finiteTarget p C X G A E i (r + 1) ⟶
    finiteTarget p C X G A E i r :=
  (DerivedCategory.TStructure.t.truncLE i).map
    (E.nearby.map ((DerivedCategory.singleFunctor (FormalNearbyCycleModels.GenericSheaves p G) 0).map
      ((K.reduction r).sheafMap i)))

/-- For every degree $i$ and modulus $r$, an isomorphism in the derived category between the
finite syntomic complex `R.finite i r` and the finite target `finiteTarget i r`, compatible with
the reduction maps $r+1 \to r$ (`modulus`). -/
structure FiniteEquivalences where
  iso : ∀ (i : ℤ) (r : ℕ), DerivedCategory.Q.obj (R.finite Q RQ i r) ≅ finiteTarget p C X G A E i r
  modulus : ∀ (i : ℤ) (r : ℕ),
    DerivedCategory.Q.map (R.reduction Q RQ i r) ≫ (iso i r).hom =
      (iso i (r + 1)).hom ≫ targetReduction p C X G A E K i r

variable
  (P : FormalProObjectSites.PointRealization p C X)
  (S : AnalyticProObjectSites.PointRealization p G)
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

def proFinite (i : ℤ) (r : ℕ) : CochainComplex (FormalProObjectSites.Sheaves p C X P) ℤ :=
  (VP.inverse.mapHomologicalComplex (.up ℤ)).obj (R.finite Q RQ i r)

def proReduction (i : ℤ) (r : ℕ) : proFinite p C B D Z T F X R Q RQ P VP i (r + 1) ⟶
    proFinite p C B D Z T F X R Q RQ P VP i r :=
  (VP.inverse.mapHomologicalComplex (.up ℤ)).map (R.reduction Q RQ i r)

def proResolvedFinite (i : ℤ) (r : ℕ) : CochainComplex (FormalProObjectSites.Sheaves p C X P) ℤ :=
  RP.functor.obj (proFinite p C B D Z T F X R Q RQ P VP i r)

def proResolvedReduction (i : ℤ) (r : ℕ) :
    proResolvedFinite p C B D Z T F X R Q RQ P VP RP i (r + 1) ⟶
      proResolvedFinite p C B D Z T F X R Q RQ P VP RP i r :=
  RP.functor.map (proReduction p C B D Z T F X R Q RQ P VP i r)

instance proCountableLimits : HasLimitsOfShape (Discrete ℕ) (FormalProObjectSites.Sheaves p C X P) := by
  let : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfShape
  exact @Sheaf.instHasLimitsOfShape.{2, 1, 1, 1, 0, 0}
    (FormalProObjectSites.ProEtaleSite p C X) inferInstance (FormalProObjectSites.topology p C X P)
      (ModuleCat.{1} ℤ) inferInstance (Discrete ℕ) inferInstance inferInstance

def proDifference (i : ℤ) :
    ∏ᶜ (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i) ⟶
      ∏ᶜ (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i) :=
  Pi.lift.{0, 1, 2} (fun r ↦
    Pi.π.{0, 1, 2} (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i) r -
    Pi.π.{0, 1, 2} (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i) (r + 1) ≫
      proResolvedReduction p C B D Z T F X R Q RQ P VP RP i r)

/-- Rlim is formed on the pro-étale site after finite pullback. -/
def integralSource (i : ℤ) : DerivedCategory (FormalProObjectSites.Sheaves p C X P) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCocone (proDifference p C B D Z T F X R Q RQ P VP RP i))

def genericProFinite (i : ℤ) (r : ℕ) :
    CochainComplex (FormalProObjectSites.GenericProModel.GenericSheaves S) ℤ :=
  (VG.inverse.mapHomologicalComplex (.up ℤ)).obj (K.finiteComplex i r)

def genericProReduction (i : ℤ) (r : ℕ) : genericProFinite p G K S VG i (r + 1) ⟶
    genericProFinite p G K S VG i r :=
  (VG.inverse.mapHomologicalComplex (.up ℤ)).map (K.transition i r)

def genericProResolvedFinite (i : ℤ) (r : ℕ) :
    CochainComplex (FormalProObjectSites.GenericProModel.GenericSheaves S) ℤ :=
  RG.functor.obj (genericProFinite p G K S VG i r)

def genericProResolvedReduction (i : ℤ) (r : ℕ) :
    genericProResolvedFinite p G K S VG RG i (r + 1) ⟶ genericProResolvedFinite p G K S VG RG i r :=
  RG.functor.map (genericProReduction p G K S VG i r)

instance genericProCountableLimits :
    HasLimitsOfShape (Discrete ℕ) (FormalProObjectSites.GenericProModel.GenericSheaves S) := by
  let : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfShape
  exact @Sheaf.instHasLimitsOfShape.{2, 1, 1, 1, 0, 0}
    (AnalyticProObjectSites.ProEtaleSite p G) inferInstance (AnalyticProObjectSites.bmsTopology p G S)
      (ModuleCat.{1} ℤ) inferInstance (Discrete ℕ) inferInstance inferInstance

def genericProDifference (i : ℤ) :
    ∏ᶜ (genericProResolvedFinite p G K S VG RG i) ⟶ ∏ᶜ (genericProResolvedFinite p G K S VG RG i) :=
  Pi.lift.{0, 1, 2} (fun r ↦ Pi.π.{0, 1, 2} (genericProResolvedFinite p G K S VG RG i) r -
    Pi.π.{0, 1, 2} (genericProResolvedFinite p G K S VG RG i) (r + 1) ≫
      genericProResolvedReduction p G K S VG RG i r)

def integralGeneric (i : ℤ) : DerivedCategory (FormalProObjectSites.GenericProModel.GenericSheaves S) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCocone (genericProDifference p G K S VG RG i))

/-- The native nearby target on the full formal pro-object site. -/
def integralTarget (i : ℤ) : DerivedCategory (FormalProObjectSites.Sheaves p C X P) :=
  (H.truncatedNearby S (R := P) i).obj (integralGeneric p G K S VG RG i)

def sourceProjection (i : ℤ) (r : ℕ) : integralSource p C B D Z T F X R Q RQ P VP RP i ⟶
    DerivedCategory.Q.obj (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i r) :=
  DerivedCategory.Q.map (CochainComplex.mappingCocone.fst
    (proDifference p C B D Z T F X R Q RQ P VP RP i) ≫
      Pi.π.{0, 1, 2} (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i) r)

def genericProjection (i : ℤ) (r : ℕ) : integralGeneric p G K S VG RG i ⟶
    DerivedCategory.Q.obj (genericProResolvedFinite p G K S VG RG i r) :=
  DerivedCategory.Q.map (CochainComplex.mappingCocone.fst
    (genericProDifference p G K S VG RG i) ≫
      Pi.π.{0, 1, 2} (genericProResolvedFinite p G K S VG RG i) r)

def finiteProTarget (i : ℤ) (r : ℕ) : DerivedCategory (FormalProObjectSites.Sheaves p C X P) :=
  (H.truncatedNearby S (R := P) i).obj (DerivedCategory.Q.obj (genericProResolvedFinite p G K S VG RG i r))

def finiteProTargetReduction (i : ℤ) (r : ℕ) : finiteProTarget p C X G A E K P S VG H RG i (r + 1) ⟶
    finiteProTarget p C X G A E K P S VG H RG i r :=
  (H.truncatedNearby S (R := P) i).map (DerivedCategory.Q.map (genericProResolvedReduction p G K S VG RG i r))

def nearbyProjection (i : ℤ) (r : ℕ) : integralTarget p C X G A E K P S VG H RG i ⟶
    finiteProTarget p C X G A E K P S VG H RG i r :=
  (H.truncatedNearby S (R := P) i).map (genericProjection p G K S VG RG i r)

set_option maxHeartbeats 2000000 in
/-- For every degree $i$ and modulus $r$, an isomorphism in the derived category between the
finite syntomic complex pulled back to the formal pro-étale site and K-injectively resolved,
`proResolvedFinite i r`, and the finite target `finiteProTarget i r`, the truncation
$\tau^{\le i}$ of the derived nearby-cycle pushforward of $\mathbb{Z}/p^{r+1}(i)$ from the
pro-étale site of the generic fibre (`finite`), compatible with the reduction maps $r+1 \to r$
(`modulus`); and, for every degree $i$, an isomorphism between `integralSource i`, the derived
limit over $r$ of the `proResolvedFinite i r`, and `integralTarget i`, the same truncated
pushforward of the derived limit over $r$ of the $\mathbb{Z}/p^{r+1}(i)$ (`integral`), compatible
with the projections to every level $r$ (`projections`). -/
structure IntegralEquivalences where
  finite : ∀ (i : ℤ) (r : ℕ),
    DerivedCategory.Q.obj (proResolvedFinite p C B D Z T F X R Q RQ P VP RP i r) ≅
      finiteProTarget p C X G A E K P S VG H RG i r
  modulus : ∀ (i : ℤ) (r : ℕ),
    DerivedCategory.Q.map (proResolvedReduction p C B D Z T F X R Q RQ P VP RP i r) ≫
      (finite i r).hom = (finite i (r + 1)).hom ≫ finiteProTargetReduction p C X G A E K P S VG H RG i r
  integral : ∀ i : ℤ,
    integralSource p C B D Z T F X R Q RQ P VP RP i ≅ integralTarget p C X G A E K P S VG H RG i
  projections : ∀ (i : ℤ) (r : ℕ),
    sourceProjection p C B D Z T F X R Q RQ P VP RP i r ≫ (finite i r).hom =
      (integral i).hom ≫ nearbyProjection p C X G A E K P S VG H RG i r

end MathlibExt.AlgebraicGeometry.SyntomicNearbyComparisons
