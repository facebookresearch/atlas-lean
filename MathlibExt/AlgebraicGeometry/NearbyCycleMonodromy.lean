/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import MathlibExt.AlgebraicGeometry.NearbyCycleComplexes

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Deck monodromy of the actual cycle cochain functors

The ordinary deck map is the adjunction mate of d followed by q = q.
A comparison for the chosen functorial resolution is normalized by its
natural quasi-isomorphism. It is generic resolution data on this actual
homeomorphism, and prevents any independent choice of a monodromy scalar.

Source: Deligne's exponential-cover construction; Dimca, §4.2;
Massey, *Notes on Perverse Sheaves and Vanishing Cycles*, the traditional
definitions and the Milnor triangle.
-/

namespace MathlibExt.AlgebraicGeometry.NearbyCycleMonodromy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization
open CategoryTheory.Functor
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ComplexAnalytification
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves
open _root_.MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleGeometry
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleComplexes

attribute [local instance] HasDerivedCategory.standard

/-- Identity-on-sections comparison for a deck homeomorphism over q. -/
def deckPushComparison {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom ⋙
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q ≅
        TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q :=
  sheafPushforwardComp d.hom q ≪≫ sheafPushforwardCongr h

/-- The normalized inverse-image comparison from the same adjunctions. -/
def deckPullComparison {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    pullback ℚ q ⋙ pullback ℚ d.hom ≅ pullback ℚ q :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) d.hom)).leftAdjointUniq
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).ofNatIsoRight
        (deckPushComparison q d h).symm)

/-- Actual deck transport q* K → d* q* K (the middle d* is direct image). -/
def deckLift {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    pullback ℚ q ≅ pullback ℚ q ⋙
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom :=
  (Functor.rightUnitor (pullback ℚ q)).symm ≪≫
    isoWhiskerLeft (pullback ℚ q)
      (asIso (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) d.hom).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (deckPullComparison q d h) _

/-- The actual ordinary deck automorphism of q* q*, fixed by the mate.
No independently selected sheaf automorphism occurs. -/
def ordinaryDeckMonodromy {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    pullback ℚ q ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q ≅
      pullback ℚ q ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q :=
  isoWhiskerRight (deckLift q d h) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (deckPushComparison q d h)

/-- Deck transport fixes the actual inverse-image/direct-image unit. -/
lemma ordinaryDeckMonodromy_unit {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).unit ≫
      (ordinaryDeckMonodromy q d h).hom =
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).unit := by
  ext F
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q
  let b := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) d.hom
  let P := pullback ℚ q
  let Q := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q
  let D := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom
  let e := deckPushComparison q d h
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (a.comp b) (a.ofNatIsoRight e.symm) F
  change (a.unit.app F ≫ Q.map (b.unit.app (P.obj F))) ≫
    Q.map (D.map ((deckPullComparison q d h).hom.app F)) =
      a.unit.app F ≫ e.inv.app (P.obj F) at hu
  change a.unit.app F ≫
    (Q.map (b.unit.app (P.obj F)) ≫
      Q.map (D.map ((deckPullComparison q d h).hom.app F)) ≫
        e.hom.app (P.obj F)) = a.unit.app F
  rw [← Category.assoc, ← Category.assoc, hu, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Actual cochain deck transport, obtained by mapping the same sheaf
natural isomorphism and its canonical composition comparison. -/
def cochainDeckLift {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    cochainPullback q ≅ cochainPullback q ⋙ cochainPushforward d.hom :=
  NatIso.mapHomologicalComplex (deckLift q d h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pullback ℚ q ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom))
        (.up ℤ)).symm

/-- The cochain direct-image comparison induced by d followed by q = q. -/
def cochainDeckPushComparison {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    cochainPushforward d.hom ⋙ cochainPushforward q ≅ cochainPushforward q :=
  Functor.mapHomologicalComplexCompIso
    (Iso.refl (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom ⋙
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (deckPushComparison q d h) (.up ℤ)

/-- Generic compatibility of the chosen resolution with this actual
homeomorphism, fixed by the natural resolution inclusion. -/
structure DeckResolutionComparison {V : TopCat.{0}} (R : FunctorialResolution V)
    (d : V ≅ V) where
  comparison : cochainPushforward d.hom ⋙ R.functor ≅
    R.functor ⋙ cochainPushforward d.hom
  inclusion_eq : ∀ K : QCochain V,
    R.inclusion.app ((cochainPushforward d.hom).obj K) ≫ comparison.hom.app K =
      (cochainPushforward d.hom).map (R.inclusion.app K)

/-- Deck transport on the resolved cover-side cochain functor. -/
def resolvedDeckLift {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) (R : FunctorialResolution V)
    (E : DeckResolutionComparison R d) :
    cochainPullback q ⋙ R.functor ≅
      (cochainPullback q ⋙ R.functor) ⋙ cochainPushforward d.hom :=
  isoWhiskerRight (cochainDeckLift q d h) R.functor ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ E.comparison ≪≫
      (Functor.associator _ _ _).symm

/-- The actual resolved deck monodromy, before restricting to the zero fiber. -/
def resolvedDeckMonodromy {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) (R : FunctorialResolution V)
    (E : DeckResolutionComparison R d) :
    cochainPullback q ⋙ R.functor ⋙ cochainPushforward q ≅
      cochainPullback q ⋙ R.functor ⋙ cochainPushforward q :=
  isoWhiskerRight (resolvedDeckLift q d h R E) (cochainPushforward q) ≪≫
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (cochainDeckPushComparison q d h)

/-- Cochain nearby monodromy for the positive generator z → z+1. -/
def nearbyCochainMonodromy {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    nearbyCochain A R ≅ nearbyCochain A R :=
  isoWhiskerRight
    (resolvedDeckMonodromy (coverProjection X s) (deckIso X s 1) (deckProjection X s 1) R E)
      (cochainPullback (spaceMap A.i))


/-- The actual integral-generator monodromy on the global nearby functor,
localized from deck translation on the exponential cover. -/
def nearbyMonodromy {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    nearbyFunctor A R ≅ nearbyFunctor A R :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
    (nearbyCochain A R ⋙ DerivedCategory.Q) (nearbyCochain A R ⋙ DerivedCategory.Q)
    _ _ (isoWhiskerRight (nearbyCochainMonodromy A R E) DerivedCategory.Q)



/-- The actual specialization arrow functor at cochain level. -/
def cochainCycleArrows {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QCochain (space X) ⥤ ComposableArrows (QCochain (space A.Z)) 1 where
  obj K := ComposableArrows.mk₁ ((specializationCochain A R).app K)
  map a := ComposableArrows.homMk₁
    ((cochainPullback (spaceMap A.i)).map a) ((nearbyCochain A R).map a)
    ((specializationCochain A R).naturality a).symm
  map_id K := by
    apply ComposableArrows.hom_ext₁
    · change (cochainPullback (spaceMap A.i)).map (𝟙 K) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
    · change (nearbyCochain A R).map (𝟙 K) = 𝟙 _
      exact CategoryTheory.Functor.map_id _ _
  map_comp a b := by
    apply ComposableArrows.hom_ext₁
    · change (cochainPullback (spaceMap A.i)).map (a ≫ b) =
        (cochainPullback (spaceMap A.i)).map a ≫ (cochainPullback (spaceMap A.i)).map b
      exact CategoryTheory.Functor.map_comp _ _ _
    · change (nearbyCochain A R).map (a ≫ b) =
        (nearbyCochain A R).map a ≫ (nearbyCochain A R).map b
      exact CategoryTheory.Functor.map_comp _ _ _

/-- Deck transport of the actual specialization arrows. The supplied
equality is the particular unit/resolution compatibility law, never an
arbitrary vanishing-cycle automorphism. -/
def cycleArrowMonodromy {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1))
    (hc : specializationCochain A R ≫ (nearbyCochainMonodromy A R E).hom =
      specializationCochain A R) :
    cochainCycleArrows A R ≅ cochainCycleArrows A R :=
  NatIso.ofComponents (fun K ↦ ComposableArrows.isoMk₁
    (Iso.refl _) ((nearbyCochainMonodromy A R E).app K) (by
      have hK := congrArg (fun a ↦ a.app K) hc
      change (specializationCochain A R).app K ≫
        (nearbyCochainMonodromy A R E).hom.app K =
          (specializationCochain A R).app K at hK
      change (specializationCochain A R).app K ≫
        (nearbyCochainMonodromy A R E).hom.app K =
          𝟙 _ ≫ (specializationCochain A R).app K
      simpa only [Category.id_comp] using hK))
    (by
      intro K L a
      apply ComposableArrows.hom_ext₁
      · change (cochainPullback (spaceMap A.i)).map a ≫ 𝟙 _ =
          𝟙 _ ≫ (cochainPullback (spaceMap A.i)).map a
        simp only [Category.comp_id, Category.id_comp]
      · change (nearbyCochain A R).map a ≫
          (nearbyCochainMonodromy A R E).hom.app L =
            (nearbyCochainMonodromy A R E).hom.app K ≫ (nearbyCochain A R).map a
        exact (nearbyCochainMonodromy A R E).hom.naturality a)

/-- Cochain vanishing monodromy is the image of the same arrow deck
automorphism under the actual mapping-cone functor. -/
def vanishingCochainMonodromy {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1))
    (hc : specializationCochain A R ≫ (nearbyCochainMonodromy A R E).hom =
      specializationCochain A R) :
    vanishingCochain A R ≅ vanishingCochain A R :=
  isoWhiskerRight (cycleArrowMonodromy A R E hc)
    (HomotopyCategory.composableArrowsFunctor (QSheaf (space A.Z)))

/-- The actual vanishing-cycle monodromy in the derived category,
localized from the functorial cochain cone deck map. -/
def vanishingMonodromy {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1))
    (hc : specializationCochain A R ≫ (nearbyCochainMonodromy A R E).hom =
      specializationCochain A R) :
    vanishingFunctor A R ≅ vanishingFunctor A R :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
    (vanishingCochain A R ⋙ DerivedCategory.Q) (vanishingCochain A R ⋙ DerivedCategory.Q)
    _ _ (isoWhiskerRight (vanishingCochainMonodromy A R E hc) DerivedCategory.Q)



/-- Ordinary cochain deck transport, with the same identity-on-sections
comparison used before deriving. -/
def ordinaryCochainDeckMonodromy {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) :
    cochainPullback q ⋙ cochainPushforward q ≅ cochainPullback q ⋙ cochainPushforward q :=
  isoWhiskerRight (cochainDeckLift q d h) (cochainPushforward q) ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (cochainDeckPushComparison q d h)

/-- The ordinary cochain unit is fixed by the actual deck transport. -/
lemma ordinaryCochainDeckMonodromy_unit {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) (K : QCochain X) :
    (cochainUnit q).app K ≫ (ordinaryCochainDeckMonodromy q d h).hom.app K =
      (cochainUnit q).app K := by
  ext n
  change (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).unit.app (K.X n) ≫
    (ordinaryDeckMonodromy q d h).hom.app (K.X n) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) q).unit.app (K.X n)
  exact congrArg (fun a ↦ a.app (K.X n)) (ordinaryDeckMonodromy_unit q d h)

/-- The normalized resolution inclusion intertwines the actual ordinary
and resolved deck maps. -/
lemma resolvedDeckMonodromy_inclusion {V X : TopCat.{0}} (q : V ⟶ X)
    (d : V ≅ V) (h : d.hom ≫ q = q) (R : FunctorialResolution V)
    (E : DeckResolutionComparison R d) (K : QCochain X) :
    (cochainPushforward q).map
        (R.inclusion.app ((cochainPullback q).obj K)) ≫
      (resolvedDeckMonodromy q d h R E).hom.app K =
    (ordinaryCochainDeckMonodromy q d h).hom.app K ≫
      (cochainPushforward q).map (R.inclusion.app ((cochainPullback q).obj K)) := by
  let p := (cochainPullback q).obj K
  let a := (cochainDeckLift q d h).hom.app K
  let B := cochainPushforward q
  let D := cochainPushforward d.hom
  let c := cochainDeckPushComparison q d h
  have h₁ : R.inclusion.app p ≫ R.functor.map a =
      a ≫ R.inclusion.app (D.obj p) := (R.inclusion.naturality a).symm
  have h₂ := E.inclusion_eq p
  have h₃ : B.map (D.map (R.inclusion.app p)) ≫ c.hom.app (R.functor.obj p) =
      c.hom.app p ≫ B.map (R.inclusion.app p) := c.hom.naturality _
  change B.map (R.inclusion.app p) ≫
    (B.map (R.functor.map a) ≫ B.map (E.comparison.hom.app p) ≫
      c.hom.app (R.functor.obj p)) =
    (B.map a ≫ c.hom.app p) ≫ B.map (R.inclusion.app p)
  have hs : R.inclusion.app p ≫ R.functor.map a ≫ E.comparison.hom.app p =
      a ≫ D.map (R.inclusion.app p) := by
    rw [← Category.assoc, h₁, Category.assoc, h₂]
  calc
    _ = B.map (R.inclusion.app p ≫ R.functor.map a ≫ E.comparison.hom.app p) ≫
        c.hom.app (R.functor.obj p) := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = B.map (a ≫ D.map (R.inclusion.app p)) ≫
        c.hom.app (R.functor.obj p) := by rw [hs]
    _ = B.map a ≫ (B.map (D.map (R.inclusion.app p)) ≫
        c.hom.app (R.functor.obj p)) := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = B.map a ≫ (c.hom.app p ≫ B.map (R.inclusion.app p)) := by rw [h₃]
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual resolution-normalized deck map fixes specialization.
This is a completed formal compatibility, used by vanishing monodromy. -/
lemma specializationDeckCompatibility {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    specializationCochain A R ≫ (nearbyCochainMonodromy A R E).hom =
      specializationCochain A R := by
  apply NatTrans.ext
  funext K
  let q := coverProjection X s
  let d := deckIso X s 1
  let I := cochainPullback (spaceMap A.i)
  let u := (cochainUnit q).app K
  let a := (cochainPushforward q).map (R.inclusion.app ((cochainPullback q).obj K))
  have he := resolvedDeckMonodromy_inclusion q d (deckProjection X s 1) R E K
  have hu := ordinaryCochainDeckMonodromy_unit q d (deckProjection X s 1) K
  change I.map (u ≫ a) ≫ I.map
    ((resolvedDeckMonodromy q d (deckProjection X s 1) R E).hom.app K) = I.map (u ≫ a)
  rw [← CategoryTheory.Functor.map_comp]
  apply congrArg I.map
  rw [Category.assoc, he, ← Category.assoc, hu]



/-- The full integral nearby-monodromy action generated by the actual
positive deck translation. -/
def nearbyMonodromyAction {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    Multiplicative ℤ →* Aut (nearbyFunctor A R) where
  toFun n := (Aut.of (nearbyMonodromy A R E)) ^ n.toAdd
  map_one' := zpow_zero _
  map_mul' m n := zpow_add (Aut.of (nearbyMonodromy A R E)) m.toAdd n.toAdd

/-- The full integral vanishing-monodromy action is generated by the
actual functorial cone deck map. -/
def vanishingMonodromyAction {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    Multiplicative ℤ →* Aut (vanishingFunctor A R) where
  toFun n :=
    (Aut.of (vanishingMonodromy A R E (specializationDeckCompatibility A R E))) ^ n.toAdd
  map_one' := zpow_zero _
  map_mul' m n := zpow_add
    (Aut.of (vanishingMonodromy A R E (specializationDeckCompatibility A R E))) m.toAdd n.toAdd

@[simp] lemma nearbyMonodromyAction_generator {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (E : DeckResolutionComparison R (deckIso X s 1)) :
    nearbyMonodromyAction A R E (Multiplicative.ofAdd (1 : ℤ)) =
      Aut.of (nearbyMonodromy A R E) :=
  zpow_one _



/-- A suitably chosen resolver together with the extra deck comparison
needed by this cochain enhancement. No existence for arbitrary resolvers
is asserted. -/
structure DeckCompatibleCycleResolution (X : ComplexScheme) (s : Γ(X.left, ⊤)) where
  resolution : FunctorialResolution (exponentialCover X s)
  comparison : DeckResolutionComparison resolution (deckIso X s 1)


end MathlibExt.AlgebraicGeometry.NearbyCycleMonodromy

