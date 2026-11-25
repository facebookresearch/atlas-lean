/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBandTwistingModels
public import MathlibExt.AlgebraicGeometry.CameralUniversalRawLiftModels

/-!
# Actual cameral restrictions and local gerbe conditions

Restrictions are native torsor and cameral pullbacks, normalized by
their original total and incidence maps. Unit and composition maps
preserve those same original maps. Local existence and local
isomorphism use actual jointly surjective étale scheme covers.
Isomorphism torsors represent the actual restricted marked arrows.
These local conclusions do not assert a global object for an
arbitrary cameral cover.
Source: DG math/0005132v3, Sections3--4/14 and Corollary4.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralGerbeFamilyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRamificationReindexing CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralBorelReductionModels CameralCentralizerBandModels
open CameralBandPullbackModels CameralBandAutomorphismModels
open CameralBandTwistingModels CameralUniversalRawLiftModels
open GroupTorsorGeometry ContractedTorsorModels ExpansionParameterModels
open TorusLineFrameModels
open CameralTorusBands

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (C : Cover F X)

attribute [local instance] centralizerGroupAction

def testBase (U : Over X.left) : Over (Spec (.of ℂ)) := (Over.map X.hom).obj U

structure RestrictionModel {U V : Over X.left} (f : V ⟶ U)
    {CU : Cover F (testBase (X := X) U)} {CV : Cover F (testBase (X := X) V)}
    (m : CameralArrow F CV CU) (H : CameralBorelAbelianizationCore.Marked F I CU)
    (H' : CameralBorelAbelianizationCore.Marked F I CV) where
  torsor : Reindex G H.regularizer.torsor ((Over.map X.hom).map f)
  comparison : H'.regularizer ≅ reindexObject G F.centralizers.scheme H.regularizer
    ((Over.map X.hom).map f) torsor
  incidence : ∀ (Z : Over (Spec (.of ℂ))) (c : Z ⟶ total F CV)
      (p : Z ⟶ H'.regularizer.torsor.total)
      (hp : p ≫ H'.regularizer.torsor.projection = c ≫ projection F CV)
      (hq : (p ≫ comparison.hom.iso.hom ≫ torsor.original G) ≫
          H.regularizer.torsor.projection = (c ≫ m.total) ≫ projection F CU),
    CameralMarkedRegularizers.incidencePoint F I CV H' Z c p hp =
    CameralMarkedRegularizers.incidencePoint F I CU H Z (c ≫ m.total)
      (p ≫ comparison.hom.iso.hom ≫ torsor.original G) hq

def RestrictionModel.original {U V : Over X.left} {f : V ⟶ U}
    {CU : Cover F (testBase (X := X) U)} {CV : Cover F (testBase (X := X) V)}
    {m : CameralArrow F CV CU} {H : CameralBorelAbelianizationCore.Marked F I CU}
    {H' : CameralBorelAbelianizationCore.Marked F I CV}
    (P : RestrictionModel F I f m H H') : H'.regularizer.torsor.total ⟶
      H.regularizer.torsor.total := P.comparison.hom.iso.hom ≫ P.torsor.original G

structure MarkedFamilies where
  cover : ∀ U : Over X.left, CameralBaseChange F C (testMap X U)
  coverMap : ∀ {U V : Over X.left} (_f : V ⟶ U),
    CameralArrow F (cover V).cover (cover U).cover
  base : ∀ {U V : Over X.left} (f : V ⟶ U), (coverMap f).base = (Over.map X.hom).map f
  original : ∀ {U V : Over X.left} (f : V ⟶ U),
    (coverMap f).total ≫ (cover U).arrow.total = (cover V).arrow.total
  weyl : ∀ {U V : Over X.left} (f : V ⟶ U) w,
    (CameralRamificationTensorModels.coverIso F (cover V).cover w).hom ≫
        (coverMap f).total =
      (coverMap f).total ≫ (CameralRamificationTensorModels.coverIso F (cover U).cover w).hom
  cover_unit : ∀ U : Over X.left, (coverMap (𝟙 U)).total = 𝟙 _
  cover_composition : ∀ {U V Z : Over X.left} (f : V ⟶ U) (g : Z ⟶ V),
    (coverMap (g ≫ f)).total = (coverMap g).total ≫ (coverMap f).total
  change : ∀ {U V : Over X.left} (_f : V ⟶ U),
    CameralBorelAbelianizationCore.Marked F I (cover U).cover ⥤
      CameralBorelAbelianizationCore.Marked F I (cover V).cover
  model : ∀ {U V : Over X.left} (f : V ⟶ U)
      (H : CameralBorelAbelianizationCore.Marked F I (cover U).cover),
    RestrictionModel F I f (coverMap f) H ((change f).obj H)
  arrows : ∀ {U V : Over X.left} (f : V ⟶ U)
      {H H' : CameralBorelAbelianizationCore.Marked F I (cover U).cover} (a : H ⟶ H'),
    ((change f).map a).map.iso.hom ≫ (model f H').original F I =
      (model f H).original F I ≫ a.map.iso.hom
  unit : ∀ U : Over X.left,
    change (𝟙 U) ≅ 𝟭 (CameralBorelAbelianizationCore.Marked F I (cover U).cover)
  unit_original : ∀ (U : Over X.left)
      (H : CameralBorelAbelianizationCore.Marked F I (cover U).cover),
    (model (𝟙 U) H).original F I = ((unit U).hom.app H).map.iso.hom
  composition : ∀ {U V Z : Over X.left} (f : V ⟶ U) (g : Z ⟶ V),
    change f ⋙ change g ≅ change (g ≫ f)
  composition_original : ∀ {U V Z : Over X.left} (f : V ⟶ U) (g : Z ⟶ V)
      (H : CameralBorelAbelianizationCore.Marked F I (cover U).cover),
    ((composition f g).hom.app H).map.iso.hom ≫ (model (g ≫ f) H).original F I =
      (model g ((change f).obj H)).original F I ≫ (model f H).original F I
  triangle : ∀ {U V : Over X.left} (f : V ⟶ U)
      (H : CameralBorelAbelianizationCore.Marked F I (cover U).cover),
    ((composition f (𝟙 V)).hom.app H).map.iso.hom ≫
      (model (𝟙 V ≫ f) H).original F I =
    ((unit V).hom.app ((change f).obj H)).map.iso.hom ≫ (model f H).original F I
  associativity : ∀ {U V Z A : Over X.left} (f : V ⟶ U) (g : Z ⟶ V) (h : A ⟶ Z)
      (H : CameralBorelAbelianizationCore.Marked F I (cover U).cover),
    (model h ((change g).obj ((change f).obj H))).original F I ≫
        ((composition f g).hom.app H).map.iso.hom ≫ (model (g ≫ f) H).original F I =
      (model h ((change g).obj ((change f).obj H))).original F I ≫
        (model g ((change f).obj H)).original F I ≫ (model f H).original F I

variable (M : MarkedFamilies F I C)

/-- A jointly surjective family of étale maps to `U`: a covering of the big étale site used by
Donagi–Gaitsgory, §3. -/
structure EtaleCover (U : Over X.left) where
  Index : Type
  piece : Index → Over X.left
  map : ∀ i, piece i ⟶ U
  etale : ∀ i, Etale (map i).left
  covers : ∀ u : U.left, ∃ i, u ∈ Set.range (map i).left

/-- The two local conditions of a gerbe on the big étale site (Donagi–Gaitsgory, §4.4): objects
exist étale locally and any two objects are étale locally isomorphic. Effective descent of
objects and arrows is not part of this statement. -/
structure LocalGerbe : Prop where
  objects : ∀ U : Over X.left, ∃ P : EtaleCover (X := X) U,
    ∀ i, Nonempty (CameralBorelAbelianizationCore.Marked F I (M.cover (P.piece i)).cover)
  isomorphisms : ∀ (U : Over X.left)
      (H H' : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover),
    ∃ P : EtaleCover (X := X) U,
      ∀ i, Nonempty ((M.change (P.map i)).obj H ≅ (M.change (P.map i)).obj H')

@[implicit_reducible] def relativeTest {U V : Over X.left} (f : V ⟶ U) :
    Over U.left := Over.mk f.left

@[instance_reducible] def localBandGroup (U : Over X.left) :
    GrpObj (F.band (testBase (X := X) U) (M.cover U).cover).scheme :=
  (F.band (testBase (X := X) U) (M.cover U).cover).group

attribute [local instance] localBandGroup

def relativeTestMap {U V Z : Over X.left} (f : V ⟶ U) (g : Z ⟶ V) :
    relativeTest (g ≫ f) ⟶ relativeTest f := Over.homMk g.left rfl

/-- The total torsor represents the actual restricted isomorphism arrows. -/
structure IsomTorsor (U : Over X.left)
    (H H' : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover) where
  torsor : Bundle (F.band (testBase (X := X) U) (M.cover U).cover).scheme
    (𝟙_ (Over U.left))
  points : ∀ {V : Over X.left} (f : V ⟶ U),
    (relativeTest f ⟶ torsor.torsor.total) ≃
      ((M.change f).obj H ⟶ (M.change f).obj H')
  naturality : ∀ {V Z : Over X.left} (f : V ⟶ U) (g : Z ⟶ V)
      (p : relativeTest f ⟶ torsor.torsor.total),
    points (g ≫ f) (relativeTestMap f g ≫ p) =
      ((M.composition f g).inv.app H) ≫
        (M.change g).map (points f p) ≫ (M.composition f g).hom.app H'

variable (BB : BorelGeometry F) (J : CentralizerGroup F)

/-- Automorphism identification is tied to actual centralizer evaluation at every base. -/
structure LocalAutomorphisms where
  comparison : ∀ (U : Over X.left)
    (H : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover),
    BandPullbackComparison F I BB J (M.cover U).cover H
  source : ∀ (U : Over X.left)
    (H : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover),
    AutomorphismSource F I BB J (M.cover U).cover H (comparison U H)
  laws : ∀ (U : Over X.left)
    (H : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover),
    AutomorphismLaws F I BB J (M.cover U).cover H (comparison U H) (source U H)

def identityCameral {Y : Over (Spec (.of ℂ))} (CY : Cover F Y) :
    total F CY ⟶ CameralTorusBands.pulled F.Weyl CY.cover
      (CameralBandAutomorphismModels.baseTest (X := Y)) :=
  Over.homMk (pullback.lift (𝟙 CY.cover.scheme.left) CY.cover.scheme.hom (by
    change (𝟙 CY.cover.scheme.left) ≫ CY.cover.scheme.hom = CY.cover.scheme.hom ≫ 𝟙 Y.left
    rw [Category.id_comp, Category.comp_id])) (by
    simp [CameralTorusBands.pulled, CameralBandAutomorphismModels.baseTest,
      total, CameralIncidenceModels.overScheme])

def sectionTorus {Y : Over (Spec (.of ℂ))} (CY : Cover F Y)
    (s : BandSections F CY) : total F CY ⟶ CameralRamificationTensorModels.Torus F :=
  identityCameral F CY ≫ ((band F CY).points (baseTest (X := Y)) s).val

def coefficientCameral {U V : Over X.left} (f : V ⟶ U) :
    total F (M.cover V).cover ⟶ CameralTorusBands.pulled F.Weyl (M.cover U).cover.cover
      (relativeTest f) :=
  Over.homMk (pullback.lift (M.coverMap f).total.left (M.cover V).cover.cover.scheme.hom
    (by
      have h' : (M.coverMap f).total ≫ projection F (M.cover U).cover =
          projection F (M.cover V).cover ≫ (Over.map X.hom).map f := by
        simpa only [M.base f] using (M.coverMap f).projection
      have h := congrArg Over.Hom.left h'
      change (M.coverMap f).total.left ≫ (M.cover U).cover.cover.scheme.hom =
        (M.cover V).cover.cover.scheme.hom ≫ f.left at h
      exact h)) (by
    change pullback.lift _ _ _ ≫
        (pullback.snd (M.cover U).cover.cover.scheme.hom f.left ≫
          f.left ≫ (testBase (X := X) U).hom) = (total F (M.cover V).cover).hom
    rw [← Category.assoc, pullback.lift_snd]
    change (M.cover V).cover.cover.scheme.hom ≫ f.left ≫ (U.hom ≫ X.hom) =
      (M.cover V).cover.cover.scheme.hom ≫ (V.hom ≫ X.hom)
    rw [← Category.assoc f.left U.hom X.hom, f.w])

/-- Every local band section pulls by its actual whole cameral coefficient map. -/
structure LocalBandRestriction where
  restrict : ∀ {U V : Over X.left} (f : V ⟶ U),
    (relativeTest f ⟶ (F.band (testBase (X := X) U) (M.cover U).cover).scheme) →
      BandSections F (M.cover V).cover
  coefficients : ∀ {U V : Over X.left} (f : V ⟶ U)
      (s : relativeTest f ⟶ (F.band (testBase (X := X) U) (M.cover U).cover).scheme),
    sectionTorus F (M.cover V).cover (restrict f s) =
      coefficientCameral F I C M f ≫
        ((F.band (testBase (X := X) U) (M.cover U).cover).points (relativeTest f) s).val

variable (L : LocalBandRestriction F I C M) (A : LocalAutomorphisms F I C M BB J)

/-- The native group and restriction operations on the represented band agree. -/
structure BandRestrictionLaws : Prop where
  identity : ∀ {U V : Over X.left} (f : V ⟶ U),
    L.restrict f (toUnit (relativeTest f) ≫
      η[(F.band (testBase (X := X) U) (M.cover U).cover).scheme]) =
        identitySection F (M.cover V).cover
  multiply : ∀ {U V : Over X.left} (f : V ⟶ U)
      (s t : relativeTest f ⟶ (F.band (testBase (X := X) U) (M.cover U).cover).scheme),
    L.restrict f (CartesianMonoidalCategory.lift s t ≫
      μ[(F.band (testBase (X := X) U) (M.cover U).cover).scheme]) =
    multiplySections F (M.cover V).cover (L.restrict f s) (L.restrict f t)
  inverse : ∀ {U V : Over X.left} (f : V ⟶ U)
      (s : relativeTest f ⟶ (F.band (testBase (X := X) U) (M.cover U).cover).scheme),
    letI := (band F (M.cover V).cover).group
    L.restrict f (s ≫ ι[(F.band (testBase (X := X) U) (M.cover U).cover).scheme]) =
      L.restrict f s ≫ ι[(band F (M.cover V).cover).scheme]

def originalSection {U V : Over X.left} (f : V ⟶ U) (s : BandSections F (M.cover U).cover) :
    relativeTest f ⟶ (band F (M.cover U).cover).scheme :=
  Over.homMk (f.left ≫ s.left) (by
    change (f.left ≫ s.left) ≫ (band F (M.cover U).cover).scheme.hom = f.left
    rw [Category.assoc, s.w]
    change f.left ≫ 𝟙 U.left = f.left
    exact Category.comp_id _)

/-- The marked arrow restriction is the original computed centralizer action. -/
def AutomorphismRestriction : Prop :=
  ∀ {U V : Over X.left} (f : V ⟶ U)
    (H : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover)
    (s : BandSections F (M.cover U).cover),
  (M.change f).map ((A.source U H).arrow s) =
    (A.source V ((M.change f).obj H)).arrow (L.restrict f (originalSection F I C M f s))

/-- The isomorphism-torsor action is actual postcomposition by that same band element. -/
structure BandedIsomTorsor (U : Over X.left)
    (H H' : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover) where
  model : IsomTorsor F I C M U H H'
  action : ∀ {V : Over X.left} (f : V ⟶ U)
      (s : relativeTest f ⟶ (band F (M.cover U).cover).scheme)
      (p : relativeTest f ⟶ model.torsor.torsor.total),
    model.points f (CartesianMonoidalCategory.lift s p ≫
      model.torsor.torsor.action.smul) =
    model.points f p ≫ (A.source V ((M.change f).obj H')).arrow (L.restrict f s)

end MathlibExt.AlgebraicGeometry.CameralGerbeFamilyModels
