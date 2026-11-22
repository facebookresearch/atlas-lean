/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Genuine Fubini for the SAME chosen filtered Nat group colimits

The actual inner quotient leg followed by the actual outer quotient
leg defines a cocone on the full Nat-by-Nat diagram. Every competing
cocone gives its genuine inner descents and then genuine outer descent;
all pair legs and uniqueness prove the whole universal property.
The actual Nat product-category swap and its identity-component source
Iso give the opposite order cocone. Both Fubini maps, all nested
quotient representatives and complete matrix-map naturalities follow.
This product-category swap supplies no native spherical permutation,
double-loop orientation, spectrum model or desired telescope law.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v uC vC
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

private theorem originalJointLegNaturality
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (x : B ⟶ E) (y : A ⟶ G) (q : G ⟶ E) (z : G ⟶ F)
    (hInner : b ≫ c = x) (hMap : y ≫ q = a ≫ x) (hOuter : q ≫ d = z) :
    (a ≫ b) ≫ (c ≫ d) = y ≫ z := by
  simp only [Category.assoc]
  rw [← Category.assoc b c d, hInner, ← Category.assoc a x d, ← hMap,
    Category.assoc, hOuter]

private theorem originalJoinedMap
    {C : Type uC} [Category.{vC} C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (r : A ⟶ F) (s : F ⟶ D) (t : F ⟶ E)
    (hMap : a ≫ b = r ≫ s) (hDesc : s ≫ c = t) : a ≫ (b ≫ c) = r ≫ t := by
  rw [← Category.assoc, hMap, Category.assoc, hDesc]

private theorem originalPairLegMap
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : B ⟶ F) (e : F ⟶ E) (f : A ⟶ G) (g : G ⟶ F)
    (hOuter : b ≫ c = d ≫ e) (hInner : a ≫ d = f ≫ g) :
    (a ≫ b) ≫ c = f ≫ (g ≫ e) := by
  rw [Category.assoc, hOuter, ← Category.assoc a d e, hInner, Category.assoc]

private theorem originalFubiniLegSquare
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ F) (e : F ⟶ E)
    (f : A ⟶ G) (g : G ⟶ D) (h : A ⟶ F) (k : G ⟶ E)
    (hMap : a ≫ b = f ≫ g) (hG : g ≫ c = k) (hF : a ≫ d = h)
    (hFlip : h ≫ e = f ≫ k) : a ≫ (b ≫ c) = a ≫ (d ≫ e) := by
  rw [← Category.assoc, hMap, Category.assoc, hG,
    ← Category.assoc a d e, hF, hFlip]

namespace GrpCat.FilteredColimits.Fubini

/-- The actual outer diagram consists of the SAME genuine inner Nat group colimits. -/
def innerColimitDiagram (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : ℕ ⥤ GrpCat.{v} :=
  F ⋙ GrpCat.FilteredColimits.colimitFunctor

/-- The full twofold colimit functor uses the SAME actual quotient construction twice. -/
def iteratedColimitFunctor : (ℕ ⥤ ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} :=
  (Functor.whiskeringRight ℕ (ℕ ⥤ GrpCat.{v}) GrpCat.{v}).obj
      GrpCat.FilteredColimits.colimitFunctor ⋙
    GrpCat.FilteredColimits.colimitFunctor

/-- Every joint leg is the actual inner quotient leg followed by the actual outer quotient leg. -/
def jointLeg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    (F.obj i).obj j ⟶ iteratedColimitFunctor.obj F :=
  (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j ≫
    (GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i

/-- ALL original pair maps preserve the actual complete inner/outer quotient leg. -/
theorem jointLeg_naturality (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) {i i' j j' : ℕ}
    (f : i ⟶ i') (g : j ⟶ j') :
    ((F.map f).app j ≫ (F.obj i').map g) ≫ jointLeg F i' j' = jointLeg F i j := by
  have hi := (GrpCat.FilteredColimits.colimitCocone (F.obj i')).w g
  have hm := GrpCat.FilteredColimits.colimitMap_ι (F.map f) j
  have ho := (GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).w f
  exact originalJointLegNaturality ((F.map f).app j) ((F.obj i').map g)
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i')).ι.app j')
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i')
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i')).ι.app j)
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j)
    (GrpCat.FilteredColimits.colimitMap (F.map f))
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i) hi hm ho

/-- The full actual pair-leg cocone keeps both original chosen group quotients. -/
def jointCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : Cocone (Functor.uncurry.obj F) where
  pt := iteratedColimitFunctor.obj F
  ι :=
    { app := fun p => jointLeg F p.1 p.2
      naturality := fun {p p'} f => by
        exact (jointLeg_naturality F f.1 f.2).trans (Category.comp_id _).symm }

/-- A competing actual pair cocone restricts to the complete original inner group diagram. -/
def restrictedInnerCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v})
    (c : Cocone (Functor.uncurry.obj F)) (i : ℕ) : Cocone (F.obj i) where
  pt := c.pt
  ι :=
    { app := fun j => c.ι.app (i, j)
      naturality := fun {j j'} g => by
        have h := c.w ((𝟙 i) ×ₘ g)
        change ((F.map (𝟙 i)).app j ≫ (F.obj i).map g) ≫ c.ι.app (i, j') =
          c.ι.app (i, j) at h
        rw [F.map_id] at h
        simp only [NatTrans.id_app, Category.id_comp] at h
        exact h.trans (Category.comp_id _).symm }

/-- Genuine inner UPL constructs each full actual original descent from a competing pair cocone. -/
def restrictedInnerDesc (F : ℕ ⥤ ℕ ⥤ GrpCat.{v})
    (c : Cocone (Functor.uncurry.obj F)) (i : ℕ) :
    GrpCat.FilteredColimits.colimit (F.obj i) ⟶ c.pt :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.obj i)).desc (restrictedInnerCocone F c i)

/-- ALL actual original inner quotient legs retain the competing full pair cocone leg. -/
theorem restrictedInnerDesc_fac (F : ℕ ⥤ ℕ ⥤ GrpCat.{v})
    (c : Cocone (Functor.uncurry.obj F)) (i j : ℕ) :
    (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j ≫ restrictedInnerDesc F c i =
      c.ι.app (i, j) :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.obj i)).fac (restrictedInnerCocone F c i) j

/-- The complete outer competing cocone uses all genuine original inner descents. -/
def outerComparisonCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v})
    (c : Cocone (Functor.uncurry.obj F)) : Cocone (innerColimitDiagram F) where
  pt := c.pt
  ι :=
    { app := restrictedInnerDesc F c
      naturality := fun {i i'} f => by
        apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.obj i)).hom_ext
        intro j
        have h := c.w (f ×ₘ (𝟙 j))
        change ((F.map f).app j ≫ (F.obj i').map (𝟙 j)) ≫ c.ι.app (i', j) =
          c.ι.app (i, j) at h
        rw [(F.obj i').map_id, Category.comp_id] at h
        let l := (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j
        have hm := GrpCat.FilteredColimits.colimitMap_ι (F.map f) j
        have hd := restrictedInnerDesc_fac F c i' j
        have hLeft : l ≫ (GrpCat.FilteredColimits.colimitMap (F.map f) ≫
            restrictedInnerDesc F c i') = c.ι.app (i, j) :=
          (originalJoinedMap l (GrpCat.FilteredColimits.colimitMap (F.map f))
            (restrictedInnerDesc F c i') ((F.map f).app j)
            ((GrpCat.FilteredColimits.colimitCocone (F.obj i')).ι.app j)
            (c.ι.app (i', j)) hm hd).trans h
        have hRight : l ≫ (restrictedInnerDesc F c i ≫ 𝟙 c.pt) = c.ι.app (i, j) :=
          (congrArg (fun m => l ≫ m) (Category.comp_id (restrictedInnerDesc F c i))).trans
            (restrictedInnerDesc_fac F c i j)
        exact hLeft.trans hRight.symm }

/-- Genuine outer UPL gives the full actual descent from the SAME chosen twofold quotient. -/
def jointDesc (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (c : Cocone (Functor.uncurry.obj F)) :
    iteratedColimitFunctor.obj F ⟶ c.pt :=
  (GrpCat.FilteredColimits.colimitCoconeIsColimit (innerColimitDiagram F)).desc
    (outerComparisonCocone F c)

/-- The full constructed descent preserves EVERY original pair of inner and outer legs. -/
theorem jointDesc_fac (F : ℕ ⥤ ℕ ⥤ GrpCat.{v})
    (c : Cocone (Functor.uncurry.obj F)) (i j : ℕ) :
    jointLeg F i j ≫ jointDesc F c = c.ι.app (i, j) := by
  have ho := (GrpCat.FilteredColimits.colimitCoconeIsColimit
    (innerColimitDiagram F)).fac (outerComparisonCocone F c) i
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m => (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j ≫ m)
      ho).trans (restrictedInnerDesc_fac F c i j))

/-- Both genuine original quotient UPLs prove the ENTIRE actual pair cocone universal property. -/
def jointCoconeIsColimit (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : IsColimit (jointCocone F) where
  desc := jointDesc F
  fac c p := jointDesc_fac F c p.1 p.2
  uniq c m hm := by
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (innerColimitDiagram F)).hom_ext
    intro i
    apply (GrpCat.FilteredColimits.colimitCoconeIsColimit (F.obj i)).hom_ext
    intro j
    exact (Category.assoc _ _ _).symm.trans
      ((hm (i, j)).trans ((jointDesc_fac F c i j).symm.trans (Category.assoc _ _ _)))

/-- The actual opposite-order cocone uses the SAME full pair source and original quotient maps. -/
def transposedJointCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : Cocone (Functor.uncurry.obj F) :=
  (Cocone.precompose (Functor.uncurryObjFlip F.flip).hom).obj
    ((jointCocone F.flip).whisker (CategoryTheory.Prod.swap ℕ ℕ))

/-- EVERY opposite-order leg keeps its actual original inner and outer quotient functions. -/
theorem transposedJointCocone_ι_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    (transposedJointCocone F).ι.app (i, j) = jointLeg F.flip j i := by
  change 𝟙 _ ≫ jointLeg F.flip j i = _
  exact Category.id_comp _

/-- Actual product-category finality and the source Iso preserve the proved opposite-order UPL. -/
def transposedJointCoconeIsColimit (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    IsColimit (transposedJointCocone F) := by
  let c := (jointCocone F.flip).whisker (CategoryTheory.Prod.swap ℕ ℕ)
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.swap ℕ ℕ)
      (jointCocone F.flip)).symm (jointCoconeIsColimit F.flip)
  exact (IsColimit.precomposeHomEquiv (Functor.uncurryObjFlip F.flip) c).symm hc

/-- BOTH complete actual Fubini maps come from the SAME genuine pair-cocone universal properties. -/
def fubiniIso (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    iteratedColimitFunctor.obj F ≅ iteratedColimitFunctor.obj F.flip :=
  (jointCoconeIsColimit F).coconePointUniqueUpToIso (transposedJointCoconeIsColimit F)

/-- The ENTIRE forward Fubini function preserves EVERY actual original pair leg. -/
theorem fubiniIso_hom_leg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    jointLeg F i j ≫ (fubiniIso F).hom = jointLeg F.flip j i :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom (jointCoconeIsColimit F)
    (transposedJointCoconeIsColimit F) (i, j)).trans (transposedJointCocone_ι_app F i j)

/-- The ENTIRE inverse Fubini function preserves EVERY actual original pair leg. -/
theorem fubiniIso_inv_leg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    jointLeg F.flip j i ≫ (fubiniIso F).inv = jointLeg F i j := by
  apply (cancel_mono (fubiniIso F).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (fubiniIso_hom_leg F i j).symm

/-- Every nested original quotient representative maps by the actual original Fubini hom. -/
theorem fubiniIso_hom_apply (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) (a : (F.obj i).obj j) :
    (fubiniIso F).hom.hom
        (GrpCat.FilteredColimits.G.mk (innerColimitDiagram F)
          ⟨i, GrpCat.FilteredColimits.G.mk (F.obj i) ⟨j, a⟩⟩) =
      GrpCat.FilteredColimits.G.mk (innerColimitDiagram F.flip)
        ⟨j, GrpCat.FilteredColimits.G.mk (F.flip.obj j) ⟨i, a⟩⟩ :=
  ConcreteCategory.congr_hom (fubiniIso_hom_leg F i j) a

/-- Every nested original quotient representative maps by the actual original Fubini inv. -/
theorem fubiniIso_inv_apply (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) (a : (F.obj i).obj j) :
    (fubiniIso F).inv.hom
        (GrpCat.FilteredColimits.G.mk (innerColimitDiagram F.flip)
          ⟨j, GrpCat.FilteredColimits.G.mk (F.flip.obj j) ⟨i, a⟩⟩) =
      GrpCat.FilteredColimits.G.mk (innerColimitDiagram F)
        ⟨i, GrpCat.FilteredColimits.G.mk (F.obj i) ⟨j, a⟩⟩ :=
  ConcreteCategory.congr_hom (fubiniIso_inv_leg F i j) a

/-- The ENTIRE actual twofold colimit map retains every original matrix map and pair leg. -/
theorem iteratedColimit_map_fac {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) (i j : ℕ) :
    jointLeg F i j ≫ iteratedColimitFunctor.map a = (a.app i).app j ≫ jointLeg G i j := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  have ho := GrpCat.FilteredColimits.colimitMap_ι (Functor.whiskerRight a Q) i
  have hi := GrpCat.FilteredColimits.colimitMap_ι (a.app i) j
  exact originalPairLegMap
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j)
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i)
    (iteratedColimitFunctor.map a) (GrpCat.FilteredColimits.colimitMap (a.app i))
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram G)).ι.app i)
    ((a.app i).app j) ((GrpCat.FilteredColimits.colimitCocone (G.obj i)).ι.app j) ho hi

/-- Every original full matrix map commutes with the ENTIRE actual forward Fubini function. -/
theorem fubiniIso_naturality {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) :
    iteratedColimitFunctor.map a ≫ (fubiniIso G).hom =
      (fubiniIso F).hom ≫ iteratedColimitFunctor.map
        ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) := by
  apply (jointCoconeIsColimit F).hom_ext
  rintro ⟨i, j⟩
  have hm := iteratedColimit_map_fac a i j
  have hG := fubiniIso_hom_leg G i j
  have hF := fubiniIso_hom_leg F i j
  have hFlip := iteratedColimit_map_fac
    ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) j i
  exact originalFubiniLegSquare (jointLeg F i j) (iteratedColimitFunctor.map a)
    ((fubiniIso G).hom) ((fubiniIso F).hom)
    (iteratedColimitFunctor.map ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a))
    ((a.app i).app j) (jointLeg G i j) (jointLeg F.flip j i) (jointLeg G.flip j i)
    hm hG hF hFlip

/-- The WHOLE genuine two-order Group colimit comparison retains every full matrix input. -/
def fubiniNatIso : iteratedColimitFunctor.{v} ≅
    CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v} ⋙ iteratedColimitFunctor :=
  NatIso.ofComponents fubiniIso (fun a => fubiniIso_naturality a)

/-- The ENTIRE natural Fubini hom function is the SAME actual pair-UPL comparison. -/
theorem fubiniNatIso_hom_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    fubiniNatIso.hom.app F = (fubiniIso F).hom := rfl

/-- The ENTIRE natural Fubini inv function is the SAME actual pair-UPL inverse comparison. -/
theorem fubiniNatIso_inv_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    fubiniNatIso.inv.app F = (fubiniIso F).inv := rfl

/-- All original matrix-map squares retain the complete actual inverse Fubini function. -/
theorem fubiniNatIso_inv_naturality {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) :
    iteratedColimitFunctor.map ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) ≫
        (fubiniIso G).inv = (fubiniIso F).inv ≫ iteratedColimitFunctor.map a :=
  fubiniNatIso.inv.naturality a

end GrpCat.FilteredColimits.Fubini
