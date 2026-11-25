/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Distributive.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Limits.Shapes.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Smash products in a pointed cartesian monoidal category

This file constructs wedge and smash products under an explicitly supplied
terminal object and returns explicit symmetric monoidal factory values.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory.Pointed

variable {C : Type u} [Category.{v} C]

/-- Actual maps out of a pushout are inverse when both original legs are fixed. -/
theorem pointedPushoutHomInvId
    {A B Z Q : C} {i : Z ⟶ A} {j : Z ⟶ B}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (h : Q ⟶ s.pt)
    (f : Under.mk h ⟶ X) (g : X ⟶ Under.mk h)
    (l : A ⟶ X.right) (r : B ⟶ X.right)
    (hfLeft : s.inl ≫ f.right = l) (hfRight : s.inr ≫ f.right = r)
    (hgLeft : l ≫ g.right = s.inl) (hgRight : r ≫ g.right = s.inr) :
    f ≫ g = 𝟙 (Under.mk h) := by
  apply Under.UnderMorphism.ext
  change f.right ≫ g.right = 𝟙 s.pt
  apply PushoutCocone.IsColimit.hom_ext hs
  · rw [← Category.assoc, hfLeft, Category.comp_id]
    exact hgLeft
  · rw [← Category.assoc, hfRight, Category.comp_id]
    exact hgRight

/-- Cancel the actual epimorphic test map using its original generator formula. -/
theorem pointedEpiInvHomId
    {Q A B : C} (X Y : Under Q) (f : X ⟶ Y) (g : Y ⟶ X)
    (q : A ⟶ X.right) (l : A ⟶ Y.right)
    (i : B ⟶ A) (t : B ⟶ Y.right) [Epi t]
    (hf : q ≫ f.right = l) (hg : t ≫ g.right = i ≫ q)
    (hi : i ≫ l = t) : g ≫ f = 𝟙 Y := by
  apply Under.UnderMorphism.ext
  change g.right ≫ f.right = 𝟙 Y.right
  apply (cancel_epi t).1
  rw [← Category.assoc, hg, Category.assoc, hf, hi, Category.comp_id]

/-- Construct the actual pointed isomorphism from its two generator laws and epi test. -/
def pointedPushoutIsoOfGeneratorData
    {A B Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ B}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (h : Q ⟶ s.pt)
    (f : Under.mk h ⟶ X) (g : X ⟶ Under.mk h)
    (l : A ⟶ X.right) (r : B ⟶ X.right)
    (hfLeft : s.inl ≫ f.right = l) (hfRight : s.inr ≫ f.right = r)
    (hgLeft : l ≫ g.right = s.inl) (hgRight : r ≫ g.right = s.inr)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) : Under.mk h ≅ X where
  hom := f
  inv := g
  hom_inv_id :=
    pointedPushoutHomInvId s hs X h f g l r hfLeft hfRight hgLeft hgRight
  inv_hom_id :=
    pointedEpiInvHomId (Under.mk h) X f g s.inl l k t hfLeft ht hk

/-- The constructed whole isomorphism has the originally supplied forward map. -/
theorem pointedPushoutIsoOfGeneratorData_hom
    {A B Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ B}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (h : Q ⟶ s.pt)
    (f : Under.mk h ⟶ X) (g : X ⟶ Under.mk h)
    (l : A ⟶ X.right) (r : B ⟶ X.right)
    (hfLeft : s.inl ≫ f.right = l) (hfRight : s.inr ≫ f.right = r)
    (hgLeft : l ≫ g.right = s.inl) (hgRight : r ≫ g.right = s.inr)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    (pointedPushoutIsoOfGeneratorData s hs X h f g l r
      hfLeft hfRight hgLeft hgRight k t ht hk).hom = f := rfl

/-- The constructed whole isomorphism has the originally supplied inverse map. -/
theorem pointedPushoutIsoOfGeneratorData_inv
    {A B Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ B}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (h : Q ⟶ s.pt)
    (f : Under.mk h ⟶ X) (g : X ⟶ Under.mk h)
    (l : A ⟶ X.right) (r : B ⟶ X.right)
    (hfLeft : s.inl ≫ f.right = l) (hfRight : s.inr ≫ f.right = r)
    (hgLeft : l ≫ g.right = s.inl) (hgRight : r ≫ g.right = s.inr)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    (pointedPushoutIsoOfGeneratorData s hs X h f g l r
      hfLeft hfRight hgLeft hgRight k t ht hk).inv = g := rfl

/-- Compute the forward pushout descent and the whole pointed isomorphism from its generators. -/
def pointedPushoutIsoOfDescentData
    {A Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ Q}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (l : A ⟶ X.right) (hc : i ≫ l = j ≫ X.hom)
    (g : X ⟶ Under.mk s.inr)
    (hgLeft : l ≫ g.right = s.inl)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) : Under.mk s.inr ≅ X := by
  let f : Under.mk s.inr ⟶ X := Under.homMk
    (PushoutCocone.IsColimit.desc hs l X.hom hc)
    (PushoutCocone.IsColimit.inr_desc hs l X.hom hc)
  have hfLeft : s.inl ≫ f.right = l :=
    PushoutCocone.IsColimit.inl_desc hs l X.hom hc
  have hfRight : s.inr ≫ f.right = X.hom :=
    PushoutCocone.IsColimit.inr_desc hs l X.hom hc
  exact pointedPushoutIsoOfGeneratorData s hs X s.inr f g l X.hom
    hfLeft hfRight hgLeft (Under.w g) k t ht hk

/-- The forward carrier map is the actual supplied pushout-colimit descent. -/
theorem pointedPushoutIsoOfDescentData_hom_right
    {A Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ Q}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (l : A ⟶ X.right) (hc : i ≫ l = j ≫ X.hom)
    (g : X ⟶ Under.mk s.inr)
    (hgLeft : l ≫ g.right = s.inl)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    (pointedPushoutIsoOfDescentData s hs X l hc g hgLeft k t ht hk).hom.right =
      PushoutCocone.IsColimit.desc hs l X.hom hc := rfl

/-- The inverse pointed map is literally the originally supplied map. -/
theorem pointedPushoutIsoOfDescentData_inv
    {A Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ Q}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (l : A ⟶ X.right) (hc : i ≫ l = j ≫ X.hom)
    (g : X ⟶ Under.mk s.inr)
    (hgLeft : l ≫ g.right = s.inl)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    (pointedPushoutIsoOfDescentData s hs X l hc g hgLeft k t ht hk).inv = g := rfl

/-- The whole computed forward map retains its product generator law. -/
theorem pointedPushoutIsoOfDescentData_inl_hom_right
    {A Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ Q}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (l : A ⟶ X.right) (hc : i ≫ l = j ≫ X.hom)
    (g : X ⟶ Under.mk s.inr)
    (hgLeft : l ≫ g.right = s.inl)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    s.inl ≫ (pointedPushoutIsoOfDescentData s hs X l hc g hgLeft k t ht hk).hom.right = l := by
  rw [pointedPushoutIsoOfDescentData_hom_right]
  exact PushoutCocone.IsColimit.inl_desc hs l X.hom hc

/-- The whole computed forward map retains its original point generator law. -/
theorem pointedPushoutIsoOfDescentData_inr_hom_right
    {A Z Q T : C} {i : Z ⟶ A} {j : Z ⟶ Q}
    (s : PushoutCocone i j) (hs : IsColimit s)
    (X : Under Q) (l : A ⟶ X.right) (hc : i ≫ l = j ≫ X.hom)
    (g : X ⟶ Under.mk s.inr)
    (hgLeft : l ≫ g.right = s.inl)
    (k : T ⟶ A) (t : T ⟶ X.right) [Epi t]
    (ht : t ≫ g.right = k ≫ s.inl) (hk : k ≫ l = t) :
    s.inr ≫ (pointedPushoutIsoOfDescentData s hs X l hc g hgLeft k t ht hk).hom.right = X.hom := by
  rw [pointedPushoutIsoOfDescentData_hom_right]
  exact PushoutCocone.IsColimit.inr_desc hs l X.hom hc

variable [CartesianMonoidalCategory C] [SymmetricCategory C]
variable [MonoidalClosed C] [HasFiniteColimits C]
variable (P : C) (hP : IsTerminal P)

set_option backward.isDefEq.respectTransparency false in
/-- The wedge of two objects under `P`. -/
noncomputable def wedge :
    Under P ⥤ Under P ⥤
      Under P where
  obj X :=
    { obj Y := Under.mk (X.hom ≫ pushout.inl X.hom Y.hom)
      map {Y Y'} g := Under.homMk
        (pushout.map X.hom Y.hom X.hom Y'.hom
          (𝟙 X.right) g.right (𝟙 P)
          (by simp) (by simpa only [Category.id_comp] using Under.w g)) (by
            dsimp
            rw [Category.assoc, pushout.inl_desc]
            simp)
      map_id Y := by
        apply Under.UnderMorphism.ext
        exact pushout.map_id
      map_comp {Y Y' Y''} g h := by
        apply Under.UnderMorphism.ext
        change
          pushout.map X.hom Y.hom X.hom Y''.hom
              (𝟙 X.right) (g.right ≫ h.right)
              (𝟙 P) (by simp)
              (by rw [← Category.assoc, Under.w g, Under.w h,
                Category.id_comp]) =
            pushout.map X.hom Y.hom X.hom Y'.hom
                (𝟙 X.right) g.right (𝟙 P)
                (by simp) (by simpa only [Category.id_comp] using Under.w g) ≫
              pushout.map X.hom Y'.hom X.hom Y''.hom
                (𝟙 X.right) h.right (𝟙 P)
                (by simp) (by simpa only [Category.id_comp] using Under.w h)
        simpa only [Category.comp_id, Category.id_comp] using
          (pushout.map_comp (𝟙 P)
            (𝟙 P) (𝟙 X.right)
            (𝟙 X.right) g.right h.right (by simp) (by simp)
            (by simp) (by simpa only [Category.id_comp] using Under.w h)).symm }
  map {X X'} f :=
    { app Y := Under.homMk
        (pushout.map X.hom Y.hom X'.hom Y.hom
          f.right (𝟙 Y.right) (𝟙 P)
          (by simpa only [Category.id_comp] using Under.w f) (by simp)) (by
            dsimp
            rw [Category.assoc, pushout.inl_desc, ← Category.assoc, Under.w f])
      naturality {Y Y'} g := by
        apply Under.UnderMorphism.ext
        apply pushout.hom_ext
        · simp
        · simp }
  map_id X := by
    apply NatTrans.ext
    funext Y
    apply Under.UnderMorphism.ext
    exact pushout.map_id
  map_comp {X X' X''} f g := by
    apply NatTrans.ext
    funext Y
    apply Under.UnderMorphism.ext
    change
      pushout.map X.hom Y.hom X''.hom Y.hom
          (f.right ≫ g.right) (𝟙 Y.right)
          (𝟙 P)
          (by rw [← Category.assoc, Under.w f, Under.w g,
            Category.id_comp]) (by simp) =
        pushout.map X.hom Y.hom X'.hom Y.hom
            f.right (𝟙 Y.right) (𝟙 P)
            (by simpa only [Category.id_comp] using Under.w f) (by simp) ≫
          pushout.map X'.hom Y.hom X''.hom Y.hom
            g.right (𝟙 Y.right) (𝟙 P)
            (by simpa only [Category.id_comp] using Under.w g) (by simp)
    simpa only [Category.comp_id, Category.id_comp] using
      (pushout.map_comp (𝟙 P)
        (𝟙 P) f.right g.right
        (𝟙 Y.right) (𝟙 Y.right)
        (by simpa only [Category.id_comp] using Under.w f) (by simp)
        (by simpa only [Category.id_comp] using Under.w g) (by simp)).symm

/-- A concrete chosen smash pushout, including its quotient leg, point leg,
and universal property. -/
noncomputable def smashPresentation (X Y : Under P) :
    Σ w : ((wedge P).obj X).obj Y ⟶
        Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom),
      Σ t : PushoutCocone w.right
        (hP.from (((wedge P).obj X).obj Y).right),
        IsColimit t := by
  let leftFace : X ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
    Under.homMk
      (CartesianMonoidalCategory.lift (𝟙 X.right)
        (hP.from X.right ≫ Y.hom)) (by
          apply CartesianMonoidalCategory.hom_ext
          · simp
          · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
            rw [← Category.assoc,
              hP.hom_ext (X.hom ≫ hP.from X.right) (𝟙 P)]
            simp)
  let rightFace : Y ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
    Under.homMk
      (CartesianMonoidalCategory.lift
        (hP.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
          apply CartesianMonoidalCategory.hom_ext
          · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
            rw [← Category.assoc,
              hP.hom_ext (Y.hom ≫ hP.from Y.right) (𝟙 P)]
            simp
          · simp)
  let w : ((wedge P).obj X).obj Y ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
    Under.homMk
      (pushout.desc leftFace.right rightFace.right (by
        exact (Under.w leftFace).trans (Under.w rightFace).symm)) (by
          change (X.hom ≫ pushout.inl X.hom Y.hom) ≫
              pushout.desc leftFace.right rightFace.right _ =
            CartesianMonoidalCategory.lift X.hom Y.hom
          rw [Category.assoc, pushout.inl_desc]
          exact Under.w leftFace)
  let c := hP.from (((wedge P).obj X).obj Y).right
  letI : HasPushout w.right c := inferInstance
  let t : PushoutCocone w.right c :=
    PushoutCocone.mk
      (pushout.inl w.right c)
      (pushout.inr w.right c)
      (pushout.condition : _)
  exact ⟨w, t, pushoutIsPushout w.right c⟩

set_option backward.isDefEq.respectTransparency false in
/-- The selected pointed object of the smash presentation. -/
noncomputable def smashObj (X Y : Under P) : Under P :=
  Under.mk
    (show P ⟶ (smashPresentation P hP X Y).2.1.pt from
      (smashPresentation P hP X Y).2.1.inr)

set_option backward.isDefEq.respectTransparency false in
/-- The map of selected smash presentations induced by two pointed maps. -/
noncomputable def smashMap {X X' Y Y' : Under P}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    smashObj P hP X Y ⟶ smashObj P hP X' Y' := by
  let p := smashPresentation P hP X Y
  let p' := smashPresentation P hP X' Y'
  let wedgeMap : ((wedge P).obj X).obj Y ⟶
      ((wedge P).obj X').obj Y' :=
    Under.homMk
      (pushout.map X.hom Y.hom X'.hom Y'.hom f.right g.right
        (𝟙 P)
        (by simpa only [Category.id_comp] using Under.w f)
        (by simpa only [Category.id_comp] using Under.w g)) (by
          dsimp [wedge]
          rw [Category.assoc, pushout.inl_desc,
            ← Category.assoc, Under.w f])
  have hProd : p.1.right ≫ (f.right ⊗ₘ g.right) =
      wedgeMap.right ≫ p'.1.right := by
    dsimp only [p, p', smashPresentation]
    dsimp only [wedgeMap, Under.homMk_right]
    apply pushout.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simp [Category.assoc]
      · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
          span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
          CartesianMonoidalCategory.lift_map, Category.id_comp, Category.assoc,
          Under.w, CartesianMonoidalCategory.lift_snd, colimit.ι_desc,
          CartesianMonoidalCategory.comp_lift, Category.comp_id]
        rw [← Category.assoc,
          hP.hom_ext (hP.from X.right)
            (f.right ≫ hP.from X'.right)]
    · apply CartesianMonoidalCategory.hom_ext
      · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
          span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
          CartesianMonoidalCategory.lift_map, Category.assoc, Under.w,
          Category.id_comp, CartesianMonoidalCategory.lift_fst, colimit.ι_desc,
          CartesianMonoidalCategory.comp_lift, Category.comp_id]
        rw [← Category.assoc,
          hP.hom_ext (hP.from Y.right)
            (g.right ≫ hP.from Y'.right)]
      · simp [Category.assoc]
  have hPoint : wedgeMap.right ≫
      hP.from (((wedge P).obj X').obj Y').right =
    hP.from (((wedge P).obj X).obj Y).right :=
    hP.hom_ext _ _
  have hCompat : p.1.right ≫
        ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl) =
      hP.from (((wedge P).obj X).obj Y).right ≫ p'.2.1.inr := by
    rw [← Category.assoc, hProd, Category.assoc, p'.2.1.condition]
    rw [← Category.assoc, hPoint]
  let t : PushoutCocone p.1.right
      (hP.from (((wedge P).obj X).obj Y).right) :=
    PushoutCocone.mk
      ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
      p'.2.1.inr hCompat
  exact Under.homMk
    (PushoutCocone.IsColimit.desc p.2.2 t.inl t.inr t.condition) (by
    exact PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)

omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- The selected smash map preserves the product quotient leg. -/
private theorem smashMap_inl {X X' Y Y' : Under P}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (smashPresentation P hP X Y).2.1.inl ≫ (smashMap P hP f g).right =
      (f.right ⊗ₘ g.right) ≫
        (smashPresentation P hP X' Y').2.1.inl := by
  dsimp only [smashMap]
  exact PushoutCocone.IsColimit.inl_desc
    (smashPresentation P hP X Y).2.2 _ _ _

omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- The selected smash map preserves the point leg. -/
private theorem smashMap_inr {X X' Y Y' : Under P}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (smashPresentation P hP X Y).2.1.inr ≫ (smashMap P hP f g).right =
      (smashPresentation P hP X' Y').2.1.inr := by
  dsimp only [smashMap]
  exact PushoutCocone.IsColimit.inr_desc
    (smashPresentation P hP X Y).2.2 _ _ _

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The selected smash map preserves the product quotient leg by tensoring the
underlying pointed maps before taking the target quotient. -/
@[reassoc]
public theorem smashMap_quotient_naturality {X X' Y Y' : Under P}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (smashPresentation P hP X Y).2.1.inl ≫ (smashMap P hP f g).right =
      (f.right ⊗ₘ g.right) ≫
        (smashPresentation P hP X' Y').2.1.inl :=
  smashMap_inl P hP f g

omit [SymmetricCategory C] [MonoidalClosed C] in
/-- The selected smash map sends the source point to the selected target point. -/
@[reassoc]
public theorem smashMap_point {X X' Y Y' : Under P}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (smashObj P hP X Y).hom ≫ (smashMap P hP f g).right =
      (smashObj P hP X' Y').hom := by
  change (smashPresentation P hP X Y).2.1.inr ≫ (smashMap P hP f g).right =
    (smashPresentation P hP X' Y').2.1.inr
  exact smashMap_inr P hP f g

set_option backward.isDefEq.respectTransparency false in
/-- The smash-product bifunctor on objects under the terminal object `P`. -/
noncomputable def smash :
    Under P ⥤ Under P ⥤ Under P := by
  exact
    { obj X :=
        { obj Y := smashObj P hP X Y
          map g := smashMap P hP (𝟙 X) g
          map_id Y := by
            apply Under.UnderMorphism.ext
            apply PushoutCocone.IsColimit.hom_ext
              (smashPresentation P hP X Y).2.2
            · rw [smashMap_inl]
              simp only [Under.id_right,
                MonoidalCategory.id_tensorHom_id, Category.id_comp]
              change (smashPresentation P hP X Y).2.1.inl =
                (smashPresentation P hP X Y).2.1.inl ≫
                  𝟙 (smashPresentation P hP X Y).2.1.pt
              rw [Category.comp_id]
            · rw [smashMap_inr]
              change (smashPresentation P hP X Y).2.1.inr =
                (smashPresentation P hP X Y).2.1.inr ≫
                  𝟙 (smashPresentation P hP X Y).2.1.pt
              rw [Category.comp_id]
          map_comp g k := by
            apply Under.UnderMorphism.ext
            change (smashMap P hP (𝟙 X) (g ≫ k)).right =
              (smashMap P hP (𝟙 X) g).right ≫
                (smashMap P hP (𝟙 X) k).right
            apply PushoutCocone.IsColimit.hom_ext
              (smashPresentation P hP X _).2.2
            · rw [smashMap_inl, ← Category.assoc, smashMap_inl,
                Category.assoc, smashMap_inl]
              rw [← Category.assoc, tensorHom_comp_tensorHom]
              simp only [Under.id_right, Under.comp_right,
                Category.id_comp]
            · rw [smashMap_inr, ← Category.assoc, smashMap_inr,
                smashMap_inr] }
      map {X X'} f :=
        { app Y := smashMap P hP f (𝟙 Y)
          naturality {Y Y'} g := by
            apply Under.UnderMorphism.ext
            change (smashMap P hP (𝟙 X) g).right ≫
                (smashMap P hP f (𝟙 Y')).right =
              (smashMap P hP f (𝟙 Y)).right ≫
                (smashMap P hP (𝟙 X') g).right
            apply PushoutCocone.IsColimit.hom_ext
              (smashPresentation P hP X Y).2.2
            · conv_lhs =>
                rw [← Category.assoc, smashMap_inl,
                  Category.assoc, smashMap_inl]
              conv_rhs =>
                rw [← Category.assoc, smashMap_inl,
                  Category.assoc, smashMap_inl]
              conv_lhs =>
                rw [← Category.assoc, tensorHom_comp_tensorHom]
              conv_rhs =>
                rw [← Category.assoc, tensorHom_comp_tensorHom]
              simp only [Under.id_right, Category.id_comp,
                Category.comp_id]
            · conv_lhs =>
                rw [← Category.assoc, smashMap_inr, smashMap_inr]
              conv_rhs =>
                rw [← Category.assoc, smashMap_inr, smashMap_inr] }
      map_id X := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change (smashMap P hP (𝟙 X) (𝟙 Y)).right =
          (Under.Hom.right (𝟙 (smashObj P hP X Y)))
        apply PushoutCocone.IsColimit.hom_ext
          (smashPresentation P hP X Y).2.2
        · rw [smashMap_inl]
          simp only [Under.id_right,
            MonoidalCategory.id_tensorHom_id, Category.id_comp]
          change (smashPresentation P hP X Y).2.1.inl =
            (smashPresentation P hP X Y).2.1.inl ≫
              𝟙 (smashPresentation P hP X Y).2.1.pt
          rw [Category.comp_id]
        · rw [smashMap_inr]
          change (smashPresentation P hP X Y).2.1.inr =
            (smashPresentation P hP X Y).2.1.inr ≫
              𝟙 (smashPresentation P hP X Y).2.1.pt
          rw [Category.comp_id]
      map_comp f g := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change (smashMap P hP (f ≫ g) (𝟙 Y)).right =
          (smashMap P hP f (𝟙 Y)).right ≫
            (smashMap P hP g (𝟙 Y)).right
        apply PushoutCocone.IsColimit.hom_ext
          (smashPresentation P hP _ Y).2.2
        · rw [smashMap_inl, ← Category.assoc, smashMap_inl,
            Category.assoc, smashMap_inl]
          rw [← Category.assoc, tensorHom_comp_tensorHom]
          simp only [Under.id_right, Under.comp_right,
            Category.comp_id]
        · rw [smashMap_inr, ← Category.assoc, smashMap_inr,
            smashMap_inr] }

/-- The smash P hP unit, the freely based point `S⁰`. -/
noncomputable def smashUnit : Under P :=
  (Under.costar P).obj P


set_option backward.isDefEq.respectTransparency false in
/-- The selected smash map induced by the Cartesian swap on the product leg. -/
noncomputable def smashSwapMap (A B : Under P) :
    ((smash P hP).obj A).obj B ⟶ ((smash P hP).obj B).obj A := by
  let pAB := smashPresentation P hP A B
  let pBA := smashPresentation P hP B A
  let wedgeSwap : ((wedge P).obj A).obj B ⟶ ((wedge P).obj B).obj A :=
    Under.homMk (pushoutSymmetry A.hom B.hom).hom (by
      dsimp [wedge]
      rw [Category.assoc, inl_comp_pushoutSymmetry_hom]
      exact pushout.condition.symm)
  let productSwap :
      Under.mk (CartesianMonoidalCategory.lift A.hom B.hom) ⟶
        Under.mk (CartesianMonoidalCategory.lift B.hom A.hom) :=
    Under.homMk (β_ A.right B.right).hom (by
      dsimp
      apply CartesianMonoidalCategory.hom_ext <;> simp)
  have hProd : pAB.1.right ≫ productSwap.right =
      wedgeSwap.right ≫ pBA.1.right := by
    dsimp only [pAB, pBA, smashPresentation]
    change pushout.desc _ _ _ ≫ (β_ A.right B.right).hom =
      (pushoutSymmetry A.hom B.hom).hom ≫ pushout.desc _ _ _
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc]
      rw [← Category.assoc]
      simp only [inl_comp_pushoutSymmetry_hom, pushout.inr_desc]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    · rw [← Category.assoc, pushout.inr_desc]
      rw [← Category.assoc]
      simp only [inr_comp_pushoutSymmetry_hom, pushout.inl_desc]
      apply CartesianMonoidalCategory.hom_ext <;> simp
  have hPoint : hP.from
        (((wedge P).obj A).obj B).right ≫ 𝟙 P =
      wedgeSwap.right ≫ hP.from
        (((wedge P).obj B).obj A).right :=
    hP.hom_ext _ _
  have hCompat : pAB.1.right ≫
        (productSwap.right ≫ pBA.2.1.inl) =
      hP.from (((wedge P).obj A).obj B).right ≫ pBA.2.1.inr := by
    rw [← Category.assoc, hProd, Category.assoc,
      pBA.2.1.condition, ← Category.assoc]
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun k => k ≫ pBA.2.1.inr) hPoint.symm
  let f : ((smash P hP).obj A).obj B ⟶
      ((smash P hP).obj B).obj A := Under.homMk
    (PushoutCocone.IsColimit.desc pAB.2.2
      (productSwap.right ≫ pBA.2.1.inl) pBA.2.1.inr hCompat) (by
        exact PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _)
  exact f

omit [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
public theorem smashSwapMap_inl (A B : Under P) :
    (smashPresentation P hP A B).2.1.inl ≫ (smashSwapMap P hP A B).right =
      (β_ A.right B.right).hom ≫ (smashPresentation P hP B A).2.1.inl := by
  dsimp only [smashSwapMap]
  exact PushoutCocone.IsColimit.inl_desc (smashPresentation P hP A B).2.2 _ _ _

omit [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
private theorem smashSwapMap_inr (A B : Under P) :
    (smashPresentation P hP A B).2.1.inr ≫ (smashSwapMap P hP A B).right =
      (smashPresentation P hP B A).2.1.inr := by
  dsimp only [smashSwapMap]
  exact PushoutCocone.IsColimit.inr_desc (smashPresentation P hP A B).2.2 _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The braiding for the generic smash product. -/
noncomputable def smashBraiding (X Y : Under P) :
    ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X := by
  let data :
      { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
        (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
          CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.snd X.right Y.right)
              (CartesianMonoidalCategory.fst X.right Y.right) ≫
            (smashPresentation P hP Y X).2.1.inl } := by
    refine ⟨{
        hom := smashSwapMap P hP X Y
        inv := smashSwapMap P hP Y X
        hom_inv_id := by
          apply Under.UnderMorphism.ext
          change (smashSwapMap P hP X Y).right ≫ (smashSwapMap P hP Y X).right =
            𝟙 (smashPresentation P hP X Y).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP X Y).2.2
          · rw [← Category.assoc, smashSwapMap_inl P hP X Y,
              Category.assoc, smashSwapMap_inl P hP Y X]
            simp
          · rw [← Category.assoc, smashSwapMap_inr P hP X Y,
              smashSwapMap_inr P hP Y X]
            change (smashPresentation P hP X Y).2.1.inr =
              (smashPresentation P hP X Y).2.1.inr ≫
                𝟙 (smashPresentation P hP X Y).2.1.pt
            rw [Category.comp_id]
        inv_hom_id := by
          apply Under.UnderMorphism.ext
          change (smashSwapMap P hP Y X).right ≫ (smashSwapMap P hP X Y).right =
            𝟙 (smashPresentation P hP Y X).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP Y X).2.2
          · rw [← Category.assoc, smashSwapMap_inl P hP Y X,
              Category.assoc, smashSwapMap_inl P hP X Y]
            simp
          · rw [← Category.assoc, smashSwapMap_inr P hP Y X,
              smashSwapMap_inr P hP X Y]
            change (smashPresentation P hP Y X).2.1.inr =
              (smashPresentation P hP Y X).2.1.inr ≫
                𝟙 (smashPresentation P hP Y X).2.1.pt
            rw [Category.comp_id]
        }, ?_⟩
    rw [smashSwapMap_inl P hP X Y,
      CartesianMonoidalCategory.lift_snd_fst]
  exact data.1

set_option backward.isDefEq.respectTransparency false in
noncomputable def smashLeftUnitor
    (X : Under P) :
    ((smash P hP).obj (smashUnit P)).obj X ≅ X := by
  let pointedProduct (P : C) : Under P ⥤ Under P ⥤ Under P :=
    { obj X :=
        { obj Y := Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
          map {Y Y'} g := Under.homMk (𝟙 X.right ⊗ₘ g.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          map_id Y := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
            exact MonoidalCategory.id_tensorHom_id _ _
          map_comp g h := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ (g.right ≫ h.right)) =
              (𝟙 X.right ⊗ₘ g.right) ≫ (𝟙 X.right ⊗ₘ h.right)
            rw [tensorHom_comp_tensorHom, Category.id_comp] }
      map {X X'} f :=
        { app Y := Under.homMk (f.right ⊗ₘ 𝟙 Y.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          naturality {Y Y'} g := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ g.right) ≫
                (f.right ⊗ₘ 𝟙 Y'.right) =
              (f.right ⊗ₘ 𝟙 Y.right) ≫
                (𝟙 X'.right ⊗ₘ g.right)
            rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
            simp }
      map_id X := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
        exact MonoidalCategory.id_tensorHom_id _ _
      map_comp f g := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change ((f.right ≫ g.right) ⊗ₘ 𝟙 Y.right) =
          (f.right ⊗ₘ 𝟙 Y.right) ≫ (g.right ⊗ₘ 𝟙 Y.right)
        rw [tensorHom_comp_tensorHom, Category.id_comp] }
  let wedgeToProduct (P : C) (hP : IsTerminal P) (X Y : Under P) :
      ((wedge P).obj X).obj Y ⟶ ((pointedProduct P).obj X).obj Y := by
    change Under.mk (X.hom ≫ pushout.inl X.hom Y.hom) ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
    let leftFace : X ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift (𝟙 X.right)
            (hP.from X.right ≫ Y.hom)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
                rw [← Category.assoc,
                  hP.hom_ext (X.hom ≫ hP.from X.right) (𝟙 P)]
                simp)
    let rightFace : Y ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift
            (hP.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
                rw [← Category.assoc,
                  hP.hom_ext (Y.hom ≫ hP.from Y.right) (𝟙 P)]
                simp
              · simp)
    exact Under.homMk
      (pushout.desc leftFace.right rightFace.right (by
        exact (Under.w leftFace).trans (Under.w rightFace).symm)) (by
          change (X.hom ≫ pushout.inl X.hom Y.hom) ≫
              pushout.desc leftFace.right rightFace.right _ =
            CartesianMonoidalCategory.lift X.hom Y.hom
          rw [Category.assoc, pushout.inl_desc]
          exact Under.w leftFace)
  let S0 : Under P := Under.mk
    (coprod.inl : P ⟶
      P ⨿ P)
  let eS0 : smashUnit P ≅ S0 := Under.isoMk (Iso.refl _) (by
    dsimp [S0, smashUnit]
    simp [Under.costar_obj_hom])
  let s0Base : P ⟶ S0.right := S0.hom
  let s0Free : P ⟶ S0.right :=
    show P ⟶
      P ⨿ P from coprod.inr
  let pointUnit : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso
      CartesianMonoidalCategory.isTerminalTensorUnit
  refine ((smash P hP).mapIso eS0).app X ≪≫ ?_
  let prodToX : S0.right ⊗ X.right ⟶ X.right :=
    (rightDistrib X.right P P).inv ≫
      coprod.desc
        (hP.from
          (P ⊗ X.right) ≫ X.hom)
        ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)
  have hLeft : pushout.inl S0.hom X.hom ≫
        (wedgeToProduct P hP S0 X).right =
      CartesianMonoidalCategory.lift (𝟙 S0.right)
        (hP.from S0.right ≫ X.hom) := by
    change pushout.inl S0.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hRight : pushout.inr S0.hom X.hom ≫
        (wedgeToProduct P hP S0 X).right =
      CartesianMonoidalCategory.lift
        (hP.from X.right ≫ S0.hom)
        (𝟙 X.right) := by
    change pushout.inr S0.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hBase : s0Base ≫
        CartesianMonoidalCategory.lift (𝟙 S0.right)
          (hP.from S0.right ≫ X.hom) =
      CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
        (s0Base ▷ X.right) := by
    dsimp [S0, s0Base]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc,
        CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.whiskerRight_snd]
      rw [← Category.assoc,
        hP.hom_ext
          (coprod.inl ≫ hP.from
            (P ⨿ P))
          (𝟙 P), Category.id_comp]
  have hFree : s0Free ≫
        CartesianMonoidalCategory.lift (𝟙 S0.right)
          (hP.from S0.right ≫ X.hom) =
      CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
        (s0Free ▷ X.right) := by
    dsimp [S0, s0Free]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc,
        CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.whiskerRight_snd]
      rw [← Category.assoc,
        hP.hom_ext
          (coprod.inr ≫ hP.from
            (P ⨿ P))
          (𝟙 P), Category.id_comp]
  have hRightBranch : CartesianMonoidalCategory.lift
      (hP.from X.right ≫ S0.hom)
        (𝟙 X.right) =
      (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
        (s0Base ▷ X.right) := by
    dsimp [S0, s0Base]
    apply CartesianMonoidalCategory.hom_ext
    · rw [CartesianMonoidalCategory.lift_fst]
      simp only [← MonoidalCategory.comp_whiskerRight,
        Category.assoc, CartesianMonoidalCategory.whiskerRight_fst]
      simpa only [Category.assoc] using congrArg
        (fun k : X.right ⟶ P ↦ k ≫ coprod.inl)
        (hP.hom_ext (hP.from X.right)
          (((λ_ X.right).inv ≫
            CartesianMonoidalCategory.fst (𝟙_ C) X.right) ≫ pointUnit.inv))
    · simp [Category.assoc]
  have hBaseEval :
      (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          (s0Base ▷ X.right)) ≫ prodToX = X.hom := by
    dsimp only [prodToX, s0Base, S0]
    calc
      (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
            (coprod.inl ▷ X.right)) ≫
          ((rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)) =
        CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          ((coprod.inl ▷ X.right) ≫
            (rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫
                (λ_ X.right).hom)) := Category.assoc _ _ _
      _ = CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          (coprod.inl ≫ coprod.desc
            (hP.from
              (P ⊗ X.right) ≫ X.hom)
            ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)) := by
        rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc]
      _ = CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          hP.from
            (P ⊗ X.right) ≫ X.hom := by
        rw [CategoryTheory.Limits.coprod.inl_desc]
      _ = X.hom := by
        rw [← Category.assoc,
          hP.hom_ext
            (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
              hP.from
                (P ⊗ X.right))
            (𝟙 P), Category.id_comp]
  have hFreeEval :
      (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          (s0Free ▷ X.right)) ≫ prodToX = X.hom := by
    dsimp only [prodToX, s0Free, S0]
    calc
      (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
            (coprod.inr ▷ X.right)) ≫
          ((rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)) =
        CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          ((coprod.inr ▷ X.right) ≫
            (rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫
                (λ_ X.right).hom)) := Category.assoc _ _ _
      _ = CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          (coprod.inr ≫ coprod.desc
            (hP.from
              (P ⊗ X.right) ≫ X.hom)
            ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)) := by
        rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc]
      _ = CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
          (pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom := by
        rw [CategoryTheory.Limits.coprod.inr_desc]
      _ = X.hom := by
        rw [CartesianMonoidalCategory.leftUnitor_hom]
        simp only [CartesianMonoidalCategory.whiskerRight_snd,
          CartesianMonoidalCategory.lift_snd]
  have hRightEval :
      ((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          (s0Base ▷ X.right)) ≫ prodToX =
        hP.from X.right ≫ X.hom := by
    dsimp only [prodToX, s0Base, S0]
    calc
      (((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
            (coprod.inl ▷ X.right)) ≫
          ((rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom))) =
        (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          ((coprod.inl ▷ X.right) ≫
            (rightDistrib X.right P
              P).inv ≫
            coprod.desc
              (hP.from
                (P ⊗ X.right) ≫ X.hom)
              ((pointUnit.hom ▷ X.right) ≫
                (λ_ X.right).hom)) := by simp only [Category.assoc]
      _ = (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          (coprod.inl ≫ coprod.desc
            (hP.from
              (P ⊗ X.right) ≫ X.hom)
            ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom)) := by
        rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc]
      _ = (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          hP.from
            (P ⊗ X.right) ≫ X.hom := by
        rw [CategoryTheory.Limits.coprod.inl_desc]
      _ = hP.from X.right ≫ X.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k : X.right ⟶ P ↦ k ≫ X.hom)
          (hP.hom_ext
            (((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right)) ≫
              hP.from (P ⊗ X.right))
            (hP.from X.right))
  let pSX := smashPresentation P hP S0 X
  let q := pSX.2.1.inl
  let b := pSX.2.1.inr
  have hLeftP : pushout.inl S0.hom X.hom ≫ pSX.1.right =
      CartesianMonoidalCategory.lift (𝟙 S0.right)
        (hP.from S0.right ≫ X.hom) := by
    dsimp only [pSX, smashPresentation]
    change pushout.inl S0.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inl_desc]
    rfl
  have hRightP : pushout.inr S0.hom X.hom ≫ pSX.1.right =
      CartesianMonoidalCategory.lift
        (hP.from X.right ≫ S0.hom) (𝟙 X.right) := by
    dsimp only [pSX, smashPresentation]
    change pushout.inr S0.hom X.hom ≫ pushout.desc _ _ _ = _
    rw [pushout.inr_desc]
    rfl
  have hCompat : pSX.1.right ≫ prodToX =
      hP.from
          (((wedge P).obj S0).obj X).right ≫ X.hom := by
    dsimp only [pSX, smashPresentation]
    apply pushout.hom_ext
    · calc
        pushout.inl S0.hom X.hom ≫
              (wedgeToProduct P hP S0 X).right ≫ prodToX =
            CartesianMonoidalCategory.lift (𝟙 S0.right)
                (hP.from S0.right ≫ X.hom) ≫
              prodToX := by
                simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ prodToX) hLeft
        _ = pushout.inl S0.hom X.hom ≫
              hP.from
                (((wedge P).obj S0).obj X).right ≫ X.hom := by
          apply coprod.hom_ext
          · calc
              s0Base ≫ CartesianMonoidalCategory.lift (𝟙 S0.right)
                    (hP.from S0.right ≫ X.hom) ≫ prodToX =
                (CartesianMonoidalCategory.lift (𝟙 P)
                    X.hom ≫ (s0Base ▷ X.right)) ≫ prodToX :=
                  by simpa only [s0Base, Category.assoc] using
                    congrArg (fun k => k ≫ prodToX) hBase
              _ = s0Base ≫ pushout.inl S0.hom X.hom ≫
                    hP.from
                      (((wedge P).obj S0).obj X).right ≫ X.hom := by
                rw [hBaseEval]
                simpa only [Category.id_comp, Category.assoc] using
                  congrArg (fun k => k ≫ X.hom)
                    (hP.hom_ext
                      (𝟙 P)
                      (s0Base ≫ pushout.inl S0.hom X.hom ≫
                        hP.from
                          (((wedge P).obj S0).obj X).right))
          · calc
              s0Free ≫ CartesianMonoidalCategory.lift (𝟙 S0.right)
                    (hP.from S0.right ≫ X.hom) ≫ prodToX =
                (CartesianMonoidalCategory.lift (𝟙 P)
                    X.hom ≫ (s0Free ▷ X.right)) ≫ prodToX :=
                  by simpa only [s0Free, Category.assoc] using
                    congrArg (fun k => k ≫ prodToX) hFree
              _ = s0Free ≫ pushout.inl S0.hom X.hom ≫
                    hP.from
                      (((wedge P).obj S0).obj X).right ≫ X.hom := by
                rw [hFreeEval]
                simpa only [Category.id_comp, Category.assoc] using
                  congrArg (fun k => k ≫ X.hom)
                    (hP.hom_ext
                      (𝟙 P)
                      (s0Free ≫ pushout.inl S0.hom X.hom ≫
                        hP.from
                          (((wedge P).obj S0).obj X).right))
    · calc
        pushout.inr S0.hom X.hom ≫
              (wedgeToProduct P hP S0 X).right ≫ prodToX =
            CartesianMonoidalCategory.lift
                (hP.from X.right ≫ S0.hom)
                (𝟙 X.right) ≫ prodToX :=
              by simpa only [Category.assoc] using
                congrArg (fun k => k ≫ prodToX) hRight
        _ = (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
              (s0Base ▷ X.right) ≫ prodToX := by
              rw [hRightBranch]
              simp only [Category.assoc]
        _ = pushout.inr S0.hom X.hom ≫
              hP.from
                (((wedge P).obj S0).obj X).right ≫ X.hom := by
          simpa only [Category.assoc] using hRightEval.trans (by
            simpa only [Category.assoc] using
              congrArg (fun k => k ≫ X.hom)
                (hP.hom_ext
                  (hP.from X.right)
                  (pushout.inr S0.hom X.hom ≫
                    hP.from
                      (((wedge P).obj S0).obj X).right)))
  have hInsert : X.hom ≫ (λ_ X.right).inv ≫
        (pointUnit.inv ▷ X.right) =
      CartesianMonoidalCategory.lift (𝟙 P) X.hom := by
    apply CartesianMonoidalCategory.hom_ext
    · apply hP.hom_ext
    · simp [Category.assoc]
  have hBackwardPoint :
      X.hom ≫ (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          (s0Free ▷ X.right) ≫ q = b := by
    calc
      X.hom ≫ (λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
            (s0Free ▷ X.right) ≫ q =
          (CartesianMonoidalCategory.lift (𝟙 P) X.hom ≫
            (s0Free ▷ X.right)) ≫ q := by
              rw [← hInsert]
              simp only [Category.assoc]
      _ = (s0Free ≫ CartesianMonoidalCategory.lift (𝟙 S0.right)
              (hP.from S0.right ≫ X.hom)) ≫ q := by
            rw [hFree]
      _ = (s0Free ≫ pushout.inl S0.hom X.hom ≫
              pSX.1.right) ≫ q := by
            rw [hLeftP]
      _ = s0Free ≫ pushout.inl S0.hom X.hom ≫
              hP.from
                (((wedge P).obj S0).obj X).right ≫ b := by
            simp only [Category.assoc]
            rw [pSX.2.1.condition]
      _ = b := by
            have hp : s0Free ≫ pushout.inl S0.hom X.hom ≫
                hP.from
                  (((wedge P).obj S0).obj X).right =
              𝟙 P :=
              hP.hom_ext _ _
            calc
              s0Free ≫ pushout.inl S0.hom X.hom ≫
                    hP.from
                      (((wedge P).obj S0).obj X).right ≫ b =
                  (𝟙 P) ≫ b :=
                by simpa only [Category.assoc] using
                  congrArg (fun k => k ≫ b) hp
              _ = b := Category.id_comp b
  let backward : X ⟶ ((smash P hP).obj S0).obj X :=
    Under.homMk
      ((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
        (s0Free ▷ X.right) ≫ q) hBackwardPoint
  let toX : P ⊗ X.right ⟶ X.right :=
    (pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom
  have hBaseProd : (s0Base ▷ X.right) ≫ prodToX =
      hP.from
        (P ⊗ X.right) ≫ X.hom := by
    have hs : s0Base = (coprod.inl : P ⟶
        P ⨿ P) := rfl
    rw [hs]
    dsimp only [prodToX]
    rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inl_desc]
  have hFreeProd : (s0Free ▷ X.right) ≫ prodToX = toX := by
    have hs : s0Free = (coprod.inr : P ⟶
        P ⨿ P) := rfl
    rw [hs]
    dsimp only [prodToX, toX]
    rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
      CategoryTheory.Limits.coprod.inr_desc]
  have hBaseFactor : toX ≫ CartesianMonoidalCategory.lift
        (hP.from X.right ≫ S0.hom)
        (𝟙 X.right) = s0Base ▷ X.right := by
    rw [hRightBranch]
    dsimp only [toX]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    slice_lhs 1 2 =>
      rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
        MonoidalCategory.id_whiskerRight]
    rw [Category.id_comp]
  have hBaseQ : (s0Base ▷ X.right) ≫ q =
      hP.from
        (P ⊗ X.right) ≫ b := by
    calc
      (s0Base ▷ X.right) ≫ q =
          (toX ≫ CartesianMonoidalCategory.lift
            (hP.from X.right ≫ S0.hom)
            (𝟙 X.right)) ≫ q := by
          rw [hBaseFactor]
      _ = toX ≫ (pushout.inr S0.hom X.hom ≫
            pSX.1.right) ≫ q := by
          simpa only [Category.assoc] using
            congrArg (fun k => (toX ≫ k) ≫ q) hRightP.symm
      _ = toX ≫ pushout.inr S0.hom X.hom ≫
            hP.from
              (((wedge P).obj S0).obj X).right ≫ b := by
          simp only [Category.assoc]
          rw [pSX.2.1.condition]
      _ = hP.from
            (P ⊗ X.right) ≫ b := by
          have hp : toX ≫ pushout.inr S0.hom X.hom ≫
                hP.from
                  (((wedge P).obj S0).obj X).right =
              hP.from
                (P ⊗ X.right) :=
            hP.hom_ext _ _
          simpa only [Category.assoc] using congrArg
            (fun k : P ⊗ X.right ⟶ P => k ≫ b) hp
  have hFreeQ : toX ≫ backward.right =
      (s0Free ▷ X.right) ≫ q := by
    change ((pointUnit.hom ▷ X.right) ≫ (λ_ X.right).hom) ≫
        ((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
          (s0Free ▷ X.right) ≫ q) =
      (s0Free ▷ X.right) ≫ q
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    slice_lhs 1 2 =>
      rw [← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
        MonoidalCategory.id_whiskerRight]
    rw [Category.id_comp]
  have hProdSection : prodToX ≫ backward.right =
      q := by
    apply (cancel_epi
      (rightDistrib X.right P P).hom).1
    apply coprod.hom_ext
    · simp only [← Category.assoc, coprod_inl_rightDistrib_hom]
      change ((s0Base ▷ X.right) ≫ prodToX) ≫
          ((λ_ X.right).inv ≫ (pointUnit.inv ▷ X.right) ≫
            (s0Free ▷ X.right) ≫ q) =
        (s0Base ▷ X.right) ≫ q
      rw [hBaseProd, Category.assoc, hBackwardPoint]
      exact hBaseQ.symm
    · simp only [← Category.assoc, coprod_inr_rightDistrib_hom]
      change ((s0Free ▷ X.right) ≫ prodToX) ≫ backward.right =
        (s0Free ▷ X.right) ≫ q
      rw [hFreeProd]
      exact hFreeQ
  let _ : Epi toX := by
    dsimp only [toX]
    infer_instance
  exact pointedPushoutIsoOfDescentData pSX.2.1 pSX.2.2 X prodToX hCompat
    backward hProdSection (s0Free ▷ X.right) toX hFreeQ hFreeProd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse generic smash left unitor inserts through the free summand
of the pointed unit and then the smash quotient. -/
theorem smashLeftUnitor_inv_free (T : Under P) :
    (smashLeftUnitor P hP T).inv.right =
      (λ_ T.right).inv ≫
        ((hP.uniqueUpToIso
          CartesianMonoidalCategory.isTerminalTensorUnit).inv ▷ T.right) ≫
        ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
        (smashPresentation P hP (smashUnit P) T).2.1.inl := by
  let S0 : Under P := Under.mk (coprod.inl : P ⟶ P ⨿ P)
  let eS0 : smashUnit P ≅ S0 := Under.isoMk (Iso.refl _) (by
    dsimp [S0, smashUnit]
    simp [Under.costar_obj_hom])
  have eS0_right : eS0.hom.right = 𝟙 _ := rfl
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  let prodTo : S0.right ⊗ T.right ⟶ T.right :=
    (rightDistrib T.right P P).inv ≫
      coprod.desc (hP.from (P ⊗ T.right) ≫ T.hom)
        ((p.hom ▷ T.right) ≫ (λ_ T.right).hom)
  have hq : q (smashUnit P) T ≫
      (((smash P hP).map eS0.hom).app T).right =
        (eS0.hom.right ⊗ₘ 𝟙 T.right) ≫ q S0 T := by
    dsimp only [q]
    unfold smash
    exact PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP (smashUnit P) T).2.2 _ _ _
  have hfree :
      ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
          q (smashUnit P) T ≫ (smashLeftUnitor P hP T).hom.right =
        (p.hom ▷ T.right) ≫ (λ_ T.right).hom := by
    dsimp only [smashLeftUnitor]
    simp only [Iso.trans_hom, Under.comp_right]
    change ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
        q (smashUnit P) T ≫
        (((smash P hP).map eS0.hom).app T).right ≫ _ = _
    slice_lhs 2 3 => rw [hq]
    rw [eS0_right]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    dsimp only [S0, q]
    simp only [pointedPushoutIsoOfDescentData_hom_right]
    calc
      _ = (coprod.inr ▷ T.right) ≫ prodTo := by
        simpa only [Category.assoc] using congrArg
          (fun k => (coprod.inr ▷ T.right) ≫ k)
          (PushoutCocone.IsColimit.inl_desc
            (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
      _ = _ := by
        dsimp only [prodTo]
        rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
          CategoryTheory.Limits.coprod.inr_desc]
  apply (cancel_mono (smashLeftUnitor P hP T).hom.right).1
  have hinvhom : (smashLeftUnitor P hP T).inv.right ≫
      (smashLeftUnitor P hP T).hom.right = 𝟙 T.right := by
    simpa only [Under.comp_right, Under.id_right] using
      congrArg Under.Hom.right (smashLeftUnitor P hP T).inv_hom_id
  rw [hinvhom]
  symm
  calc
    ((λ_ T.right).inv ≫ (p.inv ▷ T.right) ≫
          (coprod.inr ▷ T.right) ≫ q (smashUnit P) T) ≫
          (smashLeftUnitor P hP T).hom.right =
        ((λ_ T.right).inv ≫ (p.inv ▷ T.right)) ≫
          ((coprod.inr ▷ T.right) ≫ q (smashUnit P) T ≫
            (smashLeftUnitor P hP T).hom.right) := by
      simp only [Category.assoc]
    _ = ((λ_ T.right).inv ≫ (p.inv ▷ T.right)) ≫
        ((p.hom ▷ T.right) ≫ (λ_ T.right).hom) := by rw [hfree]
    _ = 𝟙 T.right := by
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
          MonoidalCategory.id_whiskerRight]
      rw [Category.id_comp, Iso.inv_hom_id]



noncomputable def smashRightUnitor
    (X : Under P) :
    ((smash P hP).obj X).obj (smashUnit P) ≅ X :=
  smashBraiding P hP X (smashUnit P) ≪≫ smashLeftUnitor P hP X


omit [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
public theorem smashBraiding_hom_quotient (X Y : Under P) :
    (smashPresentation P hP X Y).2.1.inl ≫
        (smashBraiding P hP X Y).hom.right =
      (β_ X.right Y.right).hom ≫
        (smashPresentation P hP Y X).2.1.inl := by
  unfold smash
  let pointedProduct (P : C) : Under P ⥤ Under P ⥤ Under P :=
    { obj X :=
        { obj Y := Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
          map {Y Y'} g := Under.homMk (𝟙 X.right ⊗ₘ g.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          map_id Y := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
            exact MonoidalCategory.id_tensorHom_id _ _
          map_comp g h := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ (g.right ≫ h.right)) =
              (𝟙 X.right ⊗ₘ g.right) ≫ (𝟙 X.right ⊗ₘ h.right)
            rw [tensorHom_comp_tensorHom, Category.id_comp] }
      map {X X'} f :=
        { app Y := Under.homMk (f.right ⊗ₘ 𝟙 Y.right) (by
            dsimp
            rw [CartesianMonoidalCategory.lift_map]
            simp only [Category.comp_id, Under.w])
          naturality {Y Y'} g := by
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ g.right) ≫
                (f.right ⊗ₘ 𝟙 Y'.right) =
              (f.right ⊗ₘ 𝟙 Y.right) ≫
                (𝟙 X'.right ⊗ₘ g.right)
            rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
            simp }
      map_id X := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
        exact MonoidalCategory.id_tensorHom_id _ _
      map_comp f g := by
        apply NatTrans.ext
        funext Y
        apply Under.UnderMorphism.ext
        change ((f.right ≫ g.right) ⊗ₘ 𝟙 Y.right) =
          (f.right ⊗ₘ 𝟙 Y.right) ≫ (g.right ⊗ₘ 𝟙 Y.right)
        rw [tensorHom_comp_tensorHom, Category.id_comp] }
  let wedgeToProduct (P : C) (hP : IsTerminal P) (X Y : Under P) :
      ((wedge P).obj X).obj Y ⟶ ((pointedProduct P).obj X).obj Y := by
    change Under.mk (X.hom ≫ pushout.inl X.hom Y.hom) ⟶
      Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
    let leftFace : X ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift (𝟙 X.right)
            (hP.from X.right ≫ Y.hom)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
                rw [← Category.assoc,
                  hP.hom_ext (X.hom ≫ hP.from X.right) (𝟙 P)]
                simp)
    let rightFace : Y ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
        Under.homMk
          (CartesianMonoidalCategory.lift
            (hP.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
              apply CartesianMonoidalCategory.hom_ext
              · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
                rw [← Category.assoc,
                  hP.hom_ext (Y.hom ≫ hP.from Y.right) (𝟙 P)]
                simp
              · simp)
    exact Under.homMk
      (pushout.desc leftFace.right rightFace.right (by
        exact (Under.w leftFace).trans (Under.w rightFace).symm)) (by
          change (X.hom ≫ pushout.inl X.hom Y.hom) ≫
              pushout.desc leftFace.right rightFace.right _ =
            CartesianMonoidalCategory.lift X.hom Y.hom
          rw [Category.assoc, pushout.inl_desc]
          exact Under.w leftFace)
  let data :
      { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
        (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
          CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.snd X.right Y.right)
              (CartesianMonoidalCategory.fst X.right Y.right) ≫
            (smashPresentation P hP Y X).2.1.inl } := by
    let swapMap (A B : Under P) :
        { f : ((smash P hP).obj A).obj B ⟶
            ((smash P hP).obj B).obj A //
          (smashPresentation P hP A B).2.1.inl ≫ f.right =
              (β_ A.right B.right).hom ≫
                (smashPresentation P hP B A).2.1.inl ∧
            (smashPresentation P hP A B).2.1.inr ≫ f.right =
              (smashPresentation P hP B A).2.1.inr } := by
      let pAB := smashPresentation P hP A B
      let pBA := smashPresentation P hP B A
      let wedgeSwap : ((wedge P).obj A).obj B ⟶ ((wedge P).obj B).obj A :=
        Under.homMk (pushoutSymmetry A.hom B.hom).hom (by
          dsimp [wedge]
          rw [Category.assoc, inl_comp_pushoutSymmetry_hom]
          exact pushout.condition.symm)
      let productSwap : ((pointedProduct P).obj A).obj B ⟶
          ((pointedProduct P).obj B).obj A :=
        Under.homMk (β_ A.right B.right).hom (by
          dsimp [pointedProduct]
          apply CartesianMonoidalCategory.hom_ext <;> simp)
      have hProd : pAB.1.right ≫ productSwap.right =
          wedgeSwap.right ≫ pBA.1.right := by
        dsimp only [pAB, pBA, smashPresentation]
        change pushout.desc _ _ _ ≫ (β_ A.right B.right).hom =
          (pushoutSymmetry A.hom B.hom).hom ≫ pushout.desc _ _ _
        apply pushout.hom_ext
        · rw [← Category.assoc, pushout.inl_desc]
          rw [← Category.assoc]
          simp only [inl_comp_pushoutSymmetry_hom, pushout.inr_desc]
          apply CartesianMonoidalCategory.hom_ext <;> simp
        · rw [← Category.assoc, pushout.inr_desc]
          rw [← Category.assoc]
          simp only [inr_comp_pushoutSymmetry_hom, pushout.inl_desc]
          apply CartesianMonoidalCategory.hom_ext <;> simp
      have hPoint : hP.from
            (((wedge P).obj A).obj B).right ≫ 𝟙 P =
          wedgeSwap.right ≫ hP.from
            (((wedge P).obj B).obj A).right :=
        hP.hom_ext _ _
      have hCompat : pAB.1.right ≫
            (productSwap.right ≫ pBA.2.1.inl) =
          hP.from (((wedge P).obj A).obj B).right ≫ pBA.2.1.inr := by
        rw [← Category.assoc, hProd, Category.assoc,
          pBA.2.1.condition, ← Category.assoc]
        simpa only [Category.assoc, Category.comp_id] using
          congrArg (fun k => k ≫ pBA.2.1.inr) hPoint.symm
      let f : ((smash P hP).obj A).obj B ⟶
          ((smash P hP).obj B).obj A := Under.homMk
        (PushoutCocone.IsColimit.desc pAB.2.2
          (productSwap.right ≫ pBA.2.1.inl) pBA.2.1.inr hCompat) (by
            exact PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _)
      exact ⟨f, PushoutCocone.IsColimit.inl_desc pAB.2.2 _ _ _,
        PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _⟩
    refine ⟨{
        hom := (swapMap X Y).1
        inv := (swapMap Y X).1
        hom_inv_id := by
          apply Under.UnderMorphism.ext
          change (swapMap X Y).1.right ≫ (swapMap Y X).1.right =
            𝟙 (smashPresentation P hP X Y).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP X Y).2.2
          · rw [← Category.assoc, (swapMap X Y).2.1,
              Category.assoc, (swapMap Y X).2.1]
            simp
          · rw [← Category.assoc, (swapMap X Y).2.2,
              (swapMap Y X).2.2]
            change (smashPresentation P hP X Y).2.1.inr =
              (smashPresentation P hP X Y).2.1.inr ≫
                𝟙 (smashPresentation P hP X Y).2.1.pt
            rw [Category.comp_id]
        inv_hom_id := by
          apply Under.UnderMorphism.ext
          change (swapMap Y X).1.right ≫ (swapMap X Y).1.right =
            𝟙 (smashPresentation P hP Y X).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP Y X).2.2
          · rw [← Category.assoc, (swapMap Y X).2.1,
              Category.assoc, (swapMap X Y).2.1]
            simp
          · rw [← Category.assoc, (swapMap Y X).2.2,
              (swapMap X Y).2.2]
            change (smashPresentation P hP Y X).2.1.inr =
              (smashPresentation P hP Y X).2.1.inr ≫
                𝟙 (smashPresentation P hP Y X).2.1.pt
            rw [Category.comp_id]
        }, ?_⟩
    rw [(swapMap X Y).2.1,
      CartesianMonoidalCategory.lift_snd_fst]
  have hdata : smashBraiding P hP X Y = data.1 := by
    unfold smashBraiding
    rfl
  rw [hdata]
  simpa only [CartesianMonoidalCategory.lift_snd_fst] using data.2

set_option backward.isDefEq.respectTransparency false in
/-- The inverse generic smash right unitor inserts through the free summand
of the pointed unit and then the smash quotient. -/
theorem smashRightUnitor_inv_free (X : Under P) :
    (smashRightUnitor P hP X).inv.right =
      (ρ_ X.right).inv ≫
        (X.right ◁ (hP.uniqueUpToIso
          CartesianMonoidalCategory.isTerminalTensorUnit).inv) ≫
        (X.right ◁ (coprod.inr : P ⟶ (smashUnit P).right)) ≫
        (smashPresentation P hP X (smashUnit P)).2.1.inl := by
  let p : P ≅ 𝟙_ C :=
    hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
  let free : P ⟶ (smashUnit P).right := coprod.inr
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  change (smashRightUnitor P hP X).inv.right =
    (ρ_ X.right).inv ≫ (X.right ◁ p.inv) ≫
      (X.right ◁ free) ≫ q X (smashUnit P)
  have hleft (T : Under P) :
      (free ▷ T.right) ≫ q (smashUnit P) T ≫
          (smashLeftUnitor P hP T).hom.right =
        (p.hom ▷ T.right) ≫ (λ_ T.right).hom := by
    apply (cancel_epi ((λ_ T.right).inv ≫ (p.inv ▷ T.right))).1
    simp only [Category.assoc]
    have h := smashLeftUnitor_inv_free P hP T
    change (smashLeftUnitor P hP T).inv.right =
      (λ_ T.right).inv ≫ (p.inv ▷ T.right) ≫
        (free ▷ T.right) ≫ q (smashUnit P) T at h
    rw [← reassoc_of% h, ← Under.comp_right, Iso.inv_hom_id,
      Under.id_right]
    slice_rhs 2 3 =>
      rw [← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight]
    rw [Category.id_comp, Iso.inv_hom_id]
  have hbraid (A B : Under P) :
      q A B ≫ (smashBraiding P hP A B).hom.right =
        (β_ A.right B.right).hom ≫ q B A := by
    exact smashBraiding_hom_quotient P hP A B
  have hright :
      (X.right ◁ free) ≫ q X (smashUnit P) ≫
          (smashRightUnitor P hP X).hom.right =
        (X.right ◁ p.hom) ≫ (ρ_ X.right).hom := by
    dsimp only [smashRightUnitor, Iso.trans_hom, Under.comp_right]
    slice_lhs 2 3 => rw [hbraid]
    slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_right]
    simp only [Category.assoc]
    rw [hleft]
    slice_lhs 1 2 => rw [← BraidedCategory.braiding_naturality_right]
    rw [braiding_tensorUnit_right]
    slice_lhs 3 4 => rw [Iso.inv_hom_id]
    rw [Category.comp_id]
  apply (cancel_mono (smashRightUnitor P hP X).hom.right).1
  rw [← Under.comp_right, Iso.inv_hom_id, Under.id_right]
  simp only [Category.assoc, hright]
  slice_rhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id]
  rw [Category.id_comp, Iso.inv_hom_id]


omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- The wedge's left injection maps to the left product face. -/
public theorem smashPresentation_wedge_inl (A B : Under P) :
    pushout.inl A.hom B.hom ≫ (smashPresentation P hP A B).1.right =
      CartesianMonoidalCategory.lift (𝟙 A.right) (hP.from A.right ≫ B.hom) := by
  dsimp only [smashPresentation]
  change pushout.inl A.hom B.hom ≫ pushout.desc _ _ _ = _
  rw [pushout.inl_desc]
  rfl

omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- The wedge's right injection maps to the right product face. -/
public theorem smashPresentation_wedge_inr (A B : Under P) :
    pushout.inr A.hom B.hom ≫ (smashPresentation P hP A B).1.right =
      CartesianMonoidalCategory.lift (hP.from B.right ≫ A.hom) (𝟙 B.right) := by
  dsimp only [smashPresentation]
  change pushout.inr A.hom B.hom ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc]
  rfl

omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- A product lift whose right entry is the basepoint maps to the smash point. -/
public theorem smashQuotient_lift_left (A B : Under P) {T : C} (f : T ⟶ A.right) :
    CartesianMonoidalCategory.lift f (hP.from T ≫ B.hom) ≫
        (smashPresentation P hP A B).2.1.inl =
      hP.from T ≫ (smashPresentation P hP A B).2.1.inr := by
  let collapse (A B : Under P) :=
    hP.from (((wedge P).obj A).obj B).right
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  let b (A B : Under P) :
      P ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inr
  let leftFace (A B : Under P) :=
    CartesianMonoidalCategory.lift (𝟙 A.right)
      (hP.from A.right ≫ B.hom)
  have hLeftFace (A B : Under P) :
      pushout.inl A.hom B.hom ≫
          (smashPresentation P hP A B).1.right =
        leftFace A B := by
    exact smashPresentation_wedge_inl P hP A B
  have hQLeft (A B : Under P) :
      leftFace A B ≫ q A B =
        hP.from A.right ≫ b A B := by
    rw [← hLeftFace A B, Category.assoc,
      (smashPresentation P hP A B).2.1.condition]
    have hp : pushout.inl A.hom B.hom ≫ collapse A B =
        hP.from A.right :=
      hP.hom_ext _ _
    simpa only [Category.assoc] using congrArg
      (fun k : A.right ⟶ P => k ≫ b A B) hp
  have hfac : CartesianMonoidalCategory.lift f
        (hP.from T ≫ B.hom) =
      f ≫ leftFace A B := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [leftFace]
    · simp only [leftFace, Category.assoc,
        CartesianMonoidalCategory.lift_snd]
      have hp : hP.from T =
          f ≫ hP.from A.right :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun k : T ⟶ P => k ≫ B.hom) hp
  rw [hfac, Category.assoc, hQLeft]
  have hp : f ≫ hP.from A.right =
      hP.from T :=
    hP.hom_ext _ _
  simpa only [Category.assoc] using
    congrArg (fun k : T ⟶ P => k ≫ b A B) hp

omit [SymmetricCategory C] [MonoidalClosed C] in
set_option backward.isDefEq.respectTransparency false in
/-- A product lift whose left entry is the basepoint maps to the smash point. -/
public theorem smashQuotient_lift_right (A B : Under P) {T : C} (f : T ⟶ B.right) :
    CartesianMonoidalCategory.lift (hP.from T ≫ A.hom) f ≫
        (smashPresentation P hP A B).2.1.inl =
      hP.from T ≫ (smashPresentation P hP A B).2.1.inr := by
  let collapse (A B : Under P) :=
    hP.from (((wedge P).obj A).obj B).right
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  let b (A B : Under P) :
      P ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inr
  let rightFace (A B : Under P) :=
    CartesianMonoidalCategory.lift
      (hP.from B.right ≫ A.hom) (𝟙 B.right)
  have hRightFace (A B : Under P) :
      pushout.inr A.hom B.hom ≫
          (smashPresentation P hP A B).1.right =
        rightFace A B := by
    exact smashPresentation_wedge_inr P hP A B
  have hQRight (A B : Under P) :
      rightFace A B ≫ q A B =
        hP.from B.right ≫ b A B := by
    rw [← hRightFace A B, Category.assoc,
      (smashPresentation P hP A B).2.1.condition]
    have hp : pushout.inr A.hom B.hom ≫ collapse A B =
        hP.from B.right :=
      hP.hom_ext _ _
    simpa only [Category.assoc] using congrArg
      (fun k : B.right ⟶ P => k ≫ b A B) hp
  have hfac : CartesianMonoidalCategory.lift
        (hP.from T ≫ A.hom) f =
      f ≫ rightFace A B := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [rightFace, Category.assoc,
        CartesianMonoidalCategory.lift_fst]
      have hp : hP.from T =
          f ≫ hP.from B.right :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun k : T ⟶ P => k ≫ A.hom) hp
    · simp [rightFace]
  rw [hfac, Category.assoc, hQRight]
  have hp : f ≫ hP.from B.right =
      hP.from T :=
    hP.hom_ext _ _
  simpa only [Category.assoc] using
    congrArg (fun k : T ⟶ P => k ≫ b A B) hp

set_option backward.isDefEq.respectTransparency false in
/-- The selected forward associator map together with its two-stage quotient law. -/
public noncomputable def smashAssociatorForwardData (X Y Z : Under P) :
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    { f : ((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z ⟶
        ((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z) //
      ((q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) ≫ f.right =
        (α_ X.right Y.right Z.right).hom ≫
          (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z) } := by
  dsimp only
  let collapse (A B : Under P) :=
    hP.from (((wedge P).obj A).obj B).right
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  let b (A B : Under P) :
      P ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inr
  let leftFace (A B : Under P) :=
    CartesianMonoidalCategory.lift (𝟙 A.right)
      (hP.from A.right ≫ B.hom)
  let rightFace (A B : Under P) :=
    CartesianMonoidalCategory.lift
      (hP.from B.right ≫ A.hom) (𝟙 B.right)
  have hLeftFace (A B : Under P) :
      pushout.inl A.hom B.hom ≫
          (smashPresentation P hP A B).1.right =
        leftFace A B := by
    exact smashPresentation_wedge_inl P hP A B
  have hRightFace (A B : Under P) :
      pushout.inr A.hom B.hom ≫
          (smashPresentation P hP A B).1.right =
        rightFace A B := by
    exact smashPresentation_wedge_inr P hP A B
  have hQLeftMap (A B : Under P)
      {T : C} (f : T ⟶ A.right) :
      CartesianMonoidalCategory.lift f
          (hP.from T ≫ B.hom) ≫ q A B =
        hP.from T ≫ b A B := by
    exact smashQuotient_lift_left P hP A B f
  have hQRightMap (A B : Under P)
      {T : C} (f : T ⟶ B.right) :
      CartesianMonoidalCategory.lift
          (hP.from T ≫ A.hom) f ≫ q A B =
        hP.from T ≫ b A B := by
    exact smashQuotient_lift_right P hP A B f
  let SXY := ((smash P hP).obj X).obj Y
  let SYZ := ((smash P hP).obj Y).obj Z
  let target := ((smash P hP).obj X).obj SYZ
  let qR : X.right ⊗ (Y.right ⊗ Z.right) ⟶ target.right :=
    (X.right ◁ q Y Z) ≫ q X SYZ
  let hProd : (X.right ⊗ Y.right) ⊗ Z.right ⟶ target.right :=
    (α_ X.right Y.right Z.right).hom ≫ qR
  let hPoint : P ⊗ Z.right ⟶ target.right :=
    hP.from
      (P ⊗ Z.right) ≫ target.hom
  have hPL : IsPushout
      ((smashPresentation P hP X Y).1.right ▷ Z.right)
      (collapse X Y ▷ Z.right)
      (q X Y ▷ Z.right)
      (b X Y ▷ Z.right) := by
    exact Functor.map_isPushout (tensorRight Z.right)
      (IsPushout.of_isColimit_cocone
        (smashPresentation P hP X Y).2.2)
  have hPW : IsPushout
      (X.hom ▷ Z.right) (Y.hom ▷ Z.right)
      (pushout.inl X.hom Y.hom ▷ Z.right)
      (pushout.inr X.hom Y.hom ▷ Z.right) := by
    exact Functor.map_isPushout (tensorRight Z.right)
      (IsPushout.of_hasPushout X.hom Y.hom)
  have hTripleX : (leftFace X Y ▷ Z.right) ≫
        (α_ X.right Y.right Z.right).hom =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst X.right Z.right)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst X.right Z.right ≫
            hP.from X.right ≫ Y.hom)
          (CartesianMonoidalCategory.snd X.right Z.right)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [leftFace]
    · apply CartesianMonoidalCategory.hom_ext <;>
        simp [leftFace, Category.assoc]
  have hTripleY : (rightFace X Y ▷ Z.right) ≫
        (α_ X.right Y.right Z.right).hom =
      CartesianMonoidalCategory.lift
        (hP.from (Y.right ⊗ Z.right) ≫ X.hom)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst Y.right Z.right)
          (CartesianMonoidalCategory.snd Y.right Z.right)) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc,
        CartesianMonoidalCategory.associator_hom_fst,
        CartesianMonoidalCategory.lift_fst]
      dsimp only [rightFace]
      rw [← Category.assoc,
        CartesianMonoidalCategory.whiskerRight_fst,
        Category.assoc, CartesianMonoidalCategory.lift_fst]
      have hp : CartesianMonoidalCategory.fst Y.right Z.right ≫
            hP.from Y.right =
          hP.from (Y.right ⊗ Z.right) :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using congrArg
        (fun k : Y.right ⊗ Z.right ⟶ P => k ≫ X.hom) hp
    · apply CartesianMonoidalCategory.hom_ext <;>
        simp [rightFace, Category.assoc]
  have hInnerCompat :
      ((smashPresentation P hP X Y).1.right ▷ Z.right) ≫ hProd =
        (collapse X Y ▷ Z.right) ≫ hPoint := by
    apply hPW.hom_ext
    · rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        hLeftFace]
      have hYBase : CartesianMonoidalCategory.fst X.right Z.right ≫
            hP.from X.right ≫ Y.hom =
          hP.from (X.right ⊗ Z.right) ≫ Y.hom := by
        have hp : CartesianMonoidalCategory.fst X.right Z.right ≫
              hP.from X.right =
            hP.from (X.right ⊗ Z.right) :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun k : X.right ⊗ Z.right ⟶ P =>
            k ≫ Y.hom) hp
      calc
        (leftFace X Y ▷ Z.right) ≫ hProd =
            CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst X.right Z.right)
                (CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.fst X.right Z.right ≫
                    hP.from X.right ≫ Y.hom)
                  (CartesianMonoidalCategory.snd X.right Z.right)) ≫
              (X.right ◁ q Y Z) ≫ q X SYZ := by
            dsimp only [hProd, qR]
            rw [← Category.assoc, hTripleX]
        _ = CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst X.right Z.right)
                (CartesianMonoidalCategory.lift
                    (CartesianMonoidalCategory.fst X.right Z.right ≫
                      hP.from X.right ≫ Y.hom)
                    (CartesianMonoidalCategory.snd X.right Z.right) ≫ q Y Z) ≫
              q X SYZ := by
            rw [CartesianMonoidalCategory.lift_whiskerLeft_assoc]
        _ = CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst X.right Z.right)
                (hP.from (X.right ⊗ Z.right) ≫
                  b Y Z) ≫ q X SYZ := by
            rw [hYBase, hQRightMap]
        _ = hP.from (X.right ⊗ Z.right) ≫
              b X SYZ := by
            change CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.fst X.right Z.right)
                (hP.from (X.right ⊗ Z.right) ≫
                  SYZ.hom) ≫ q X SYZ = _
            exact hQLeftMap X SYZ _
        _ = (pushout.inl X.hom Y.hom ▷ Z.right) ≫
              (collapse X Y ▷ Z.right) ≫ hPoint := by
            change hP.from (X.right ⊗ Z.right) ≫
                target.hom =
              (pushout.inl X.hom Y.hom ▷ Z.right) ≫
                (collapse X Y ▷ Z.right) ≫
                hP.from
                  (P ⊗ Z.right) ≫ target.hom
            have hp : hP.from (X.right ⊗ Z.right) =
                (pushout.inl X.hom Y.hom ▷ Z.right) ≫
                  (collapse X Y ▷ Z.right) ≫
                  hP.from
                    (P ⊗ Z.right) :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : X.right ⊗ Z.right ⟶
                P => k ≫ target.hom) hp
    · rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        hRightFace]
      calc
        (rightFace X Y ▷ Z.right) ≫ hProd =
            CartesianMonoidalCategory.lift
                (hP.from (Y.right ⊗ Z.right) ≫
                  X.hom)
                (CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.fst Y.right Z.right)
                  (CartesianMonoidalCategory.snd Y.right Z.right)) ≫
              (X.right ◁ q Y Z) ≫ q X SYZ := by
            dsimp only [hProd, qR]
            rw [← Category.assoc, hTripleY]
        _ = CartesianMonoidalCategory.lift
                (hP.from (Y.right ⊗ Z.right) ≫
                  X.hom)
                (CartesianMonoidalCategory.lift
                    (CartesianMonoidalCategory.fst Y.right Z.right)
                    (CartesianMonoidalCategory.snd Y.right Z.right) ≫ q Y Z) ≫
              q X SYZ := by
            rw [CartesianMonoidalCategory.lift_whiskerLeft_assoc]
        _ = CartesianMonoidalCategory.lift
                (hP.from (Y.right ⊗ Z.right) ≫
                  X.hom) (q Y Z) ≫ q X SYZ := by
            rw [CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]
        _ = hP.from (Y.right ⊗ Z.right) ≫
              b X SYZ := hQRightMap X SYZ _
        _ = (pushout.inr X.hom Y.hom ▷ Z.right) ≫
              (collapse X Y ▷ Z.right) ≫ hPoint := by
            change hP.from (Y.right ⊗ Z.right) ≫
                target.hom =
              (pushout.inr X.hom Y.hom ▷ Z.right) ≫
                (collapse X Y ▷ Z.right) ≫
                hP.from
                  (P ⊗ Z.right) ≫ target.hom
            have hp : hP.from (Y.right ⊗ Z.right) =
                (pushout.inr X.hom Y.hom ▷ Z.right) ≫
                  (collapse X Y ▷ Z.right) ≫
                  hP.from
                    (P ⊗ Z.right) :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : Y.right ⊗ Z.right ⟶
                P => k ≫ target.hom) hp
  let insertZ : X.right ⊗ Y.right ⟶
      (X.right ⊗ Y.right) ⊗ Z.right :=
    CartesianMonoidalCategory.lift (𝟙 (X.right ⊗ Y.right))
      (hP.from (X.right ⊗ Y.right) ≫ Z.hom)
  have hTripleZ : insertZ ≫ (α_ X.right Y.right Z.right).hom =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst X.right Y.right)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.snd X.right Y.right)
          (hP.from (X.right ⊗ Y.right) ≫
            Z.hom)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [insertZ]
    · apply CartesianMonoidalCategory.hom_ext
      · simp [insertZ]
      · simp [insertZ]
  have hZBase : insertZ ≫ hProd =
      hP.from (X.right ⊗ Y.right) ≫
        target.hom := by
    calc
      insertZ ≫ hProd =
          CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst X.right Y.right)
              (CartesianMonoidalCategory.lift
                (CartesianMonoidalCategory.snd X.right Y.right)
                (hP.from (X.right ⊗ Y.right) ≫
                  Z.hom)) ≫
            (X.right ◁ q Y Z) ≫ q X SYZ := by
          dsimp only [hProd, qR]
          rw [← Category.assoc, hTripleZ]
      _ = CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst X.right Y.right)
              (CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.snd X.right Y.right)
                  (hP.from (X.right ⊗ Y.right) ≫
                    Z.hom) ≫ q Y Z) ≫ q X SYZ := by
          rw [CartesianMonoidalCategory.lift_whiskerLeft_assoc]
      _ = CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst X.right Y.right)
              (hP.from (X.right ⊗ Y.right) ≫
                b Y Z) ≫ q X SYZ := by
          rw [hQLeftMap]
      _ = hP.from (X.right ⊗ Y.right) ≫
            b X SYZ := by
          change CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.fst X.right Y.right)
              (hP.from (X.right ⊗ Y.right) ≫
                SYZ.hom) ≫ q X SYZ = _
          exact hQLeftMap X SYZ _
      _ = hP.from (X.right ⊗ Y.right) ≫
            target.hom := rfl
  let innerDesc : SXY.right ⊗ Z.right ⟶ target.right :=
    hPL.desc hProd hPoint hInnerCompat
  have hInnerInl : (q X Y ▷ Z.right) ≫ innerDesc = hProd :=
    hPL.inl_desc hProd hPoint hInnerCompat
  have hInnerInr : (b X Y ▷ Z.right) ≫ innerDesc = hPoint :=
    hPL.inr_desc hProd hPoint hInnerCompat
  have hInsertRight {A B : C} (f : A ⟶ B) :
      f ≫ CartesianMonoidalCategory.lift (𝟙 B)
          (hP.from B ≫ Z.hom) =
        CartesianMonoidalCategory.lift (𝟙 A)
            (hP.from A ≫ Z.hom) ≫
          (f ▷ Z.right) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.whiskerRight_snd]
      have hp : f ≫ hP.from B =
          hP.from A :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun k : A ⟶ P => k ≫ Z.hom) hp
  have hInsertQ : q X Y ≫ leftFace SXY Z =
      insertZ ≫ (q X Y ▷ Z.right) := by
    dsimp only [leftFace, insertZ, SXY]
    exact hInsertRight (q X Y)
  let insertPoint : P ⟶
      P ⊗ Z.right :=
    CartesianMonoidalCategory.lift (𝟙 P)
      (hP.from P ≫ Z.hom)
  have hInsertB : b X Y ≫ leftFace SXY Z =
      insertPoint ≫ (b X Y ▷ Z.right) := by
    dsimp only [leftFace, insertPoint, SXY]
    exact hInsertRight (b X Y)
  have hOuterLeft : leftFace SXY Z ≫ innerDesc =
      hP.from SXY.right ≫ target.hom := by
    apply pushout.hom_ext
    · calc
        q X Y ≫ leftFace SXY Z ≫ innerDesc =
            insertZ ≫ (q X Y ▷ Z.right) ≫ innerDesc := by
              rw [← Category.assoc, hInsertQ, Category.assoc]
        _ = insertZ ≫ hProd := by rw [hInnerInl]
        _ = hP.from (X.right ⊗ Y.right) ≫
              target.hom := hZBase
        _ = q X Y ≫ hP.from SXY.right ≫
              target.hom := by
            have hp : hP.from (X.right ⊗ Y.right) =
                q X Y ≫ hP.from SXY.right :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : X.right ⊗ Y.right ⟶
                P => k ≫ target.hom) hp
    · calc
        b X Y ≫ leftFace SXY Z ≫ innerDesc =
            insertPoint ≫ (b X Y ▷ Z.right) ≫ innerDesc := by
              rw [← Category.assoc, hInsertB, Category.assoc]
        _ = insertPoint ≫ hPoint := by rw [hInnerInr]
        _ = hP.from P ≫
              target.hom := by
            change insertPoint ≫
                  hP.from
                    (P ⊗ Z.right) ≫ target.hom = _
            have hp : insertPoint ≫ hP.from
                  (P ⊗ Z.right) =
                hP.from P :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : P ⟶
                P => k ≫ target.hom) hp
        _ = b X Y ≫ hP.from SXY.right ≫
              target.hom := by
            have hp : hP.from P =
                b X Y ≫ hP.from SXY.right :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : P ⟶
                P => k ≫ target.hom) hp
  let pointInsert : Z.right ⟶ P ⊗ Z.right :=
    CartesianMonoidalCategory.lift
      (hP.from Z.right) (𝟙 Z.right)
  have hPointInsert : pointInsert ≫ (b X Y ▷ Z.right) =
      CartesianMonoidalCategory.lift
        (hP.from Z.right ≫ b X Y)
        (𝟙 Z.right) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [pointInsert]
    · simp [pointInsert]
  have hOuterRight : rightFace SXY Z ≫ innerDesc =
      hP.from Z.right ≫ target.hom := by
    change CartesianMonoidalCategory.lift
        (hP.from Z.right ≫ b X Y)
        (𝟙 Z.right) ≫ innerDesc = _
    rw [← hPointInsert, Category.assoc, hInnerInr]
    change pointInsert ≫ hP.from
          (P ⊗ Z.right) ≫ target.hom = _
    have hp : pointInsert ≫ hP.from
          (P ⊗ Z.right) =
        hP.from Z.right :=
      hP.hom_ext _ _
    simpa only [Category.assoc] using
      congrArg (fun k : Z.right ⟶ P => k ≫ target.hom) hp
  have hOuterCompat :
      (smashPresentation P hP SXY Z).1.right ≫ innerDesc =
      collapse SXY Z ≫ target.hom := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hLeftFace, hOuterLeft]
      have hp : hP.from SXY.right =
          pushout.inl SXY.hom Z.hom ≫ collapse SXY Z :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun k : SXY.right ⟶ P =>
          k ≫ target.hom) hp
    · rw [← Category.assoc, hRightFace, hOuterRight]
      have hp : hP.from Z.right =
          pushout.inr SXY.hom Z.hom ≫ collapse SXY Z :=
        hP.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun k : Z.right ⟶ P =>
          k ≫ target.hom) hp
  let forward :
      { f : ((smash P hP).obj SXY).obj Z ⟶ target //
        q SXY Z ≫ f.right = innerDesc } := by
    let f : ((smash P hP).obj SXY).obj Z ⟶ target := Under.homMk
      (PushoutCocone.IsColimit.desc
        (smashPresentation P hP SXY Z).2.2
        innerDesc target.hom hOuterCompat) (by
          exact PushoutCocone.IsColimit.inr_desc
            (smashPresentation P hP SXY Z).2.2 _ _ _)
    exact ⟨f, PushoutCocone.IsColimit.inl_desc
      (smashPresentation P hP SXY Z).2.2 _ _ _⟩
  refine ⟨forward.1, ?_⟩
  change ((q X Y ▷ Z.right) ≫ q SXY Z) ≫
      forward.1.right = hProd
  rw [Category.assoc, forward.2]
  exact hInnerInl

set_option backward.isDefEq.respectTransparency false in
/-- The selected reverse associator map, with the original five-factor braid route. -/
public noncomputable def smashAssociatorBackwardMap (X Y Z : Under P) :
    ((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z) ⟶
    ((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z :=
  ((smash P hP).obj X).map (smashBraiding P hP Y Z).hom ≫
    (smashBraiding P hP X (((smash P hP).obj Z).obj Y)).hom ≫
    (smashAssociatorForwardData P hP Z Y X).1 ≫
    ((smash P hP).obj Z).map (smashBraiding P hP Y X).hom ≫
    (smashBraiding P hP Z (((smash P hP).obj X).obj Y)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The selected reverse map has the inverse base-associator quotient formula. -/
public theorem smashAssociatorBackwardMap_quotient (X Y Z : Under P) :
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    ((X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ≫
        (smashAssociatorBackwardMap P hP X Y Z).right =
      (α_ X.right Y.right Z.right).inv ≫
        (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z := by
  dsimp only
  let braidingData (A B : Under P) :
      { e : ((smash P hP).obj A).obj B ≅ ((smash P hP).obj B).obj A //
        (smashPresentation P hP A B).2.1.inl ≫ e.hom.right =
          CartesianMonoidalCategory.lift
              (CartesianMonoidalCategory.snd A.right B.right)
              (CartesianMonoidalCategory.fst A.right B.right) ≫
            (smashPresentation P hP B A).2.1.inl } :=
    ⟨smashBraiding P hP A B, by
      change (smashPresentation P hP A B).2.1.inl ≫
          (smashSwapMap P hP A B).right = _
      simpa only [CartesianMonoidalCategory.lift_snd_fst] using
        smashSwapMap_inl P hP A B⟩
  let collapse (A B : Under P) :=
    hP.from (((wedge P).obj A).obj B).right
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  let b (A B : Under P) :
      P ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inr
  let assocHom := smashAssociatorForwardData P hP
  have assocHom_q (A B C : Under P) :
      ((q A B ▷ C.right) ≫ q (((smash P hP).obj A).obj B) C) ≫
          (assocHom A B C).1.right =
        (α_ A.right B.right C.right).hom ≫
          (A.right ◁ q B C) ≫ q A (((smash P hP).obj B).obj C) := by
    exact (assocHom A B C).2
  let backward := smashAssociatorBackwardMap P hP X Y Z
  have smashMap_q (A : Under P) {B B' : Under P}
      (g : B ⟶ B') :
      q A B ≫ (((smash P hP).obj A).map g).right =
        (𝟙 A.right ⊗ₘ g.right) ≫ q A B' := by
    dsimp only [q]
    unfold smash
    dsimp only
    let p := smashPresentation P hP A B
    let p' := smashPresentation P hP A B'
    change p.2.1.inl ≫ p.2.2.desc
        (PushoutCocone.mk
          ((Under.Hom.right (𝟙 A) ⊗ₘ g.right) ≫ p'.2.1.inl)
          p'.2.1.inr _) =
      (𝟙 A.right ⊗ₘ g.right) ≫ p'.2.1.inl
    exact PushoutCocone.IsColimit.inl_desc p.2.2 _ _ _
  have braiding_q (A B : Under P) :
      q A B ≫ (braidingData A B).1.hom.right =
        (β_ A.right B.right).hom ≫ q B A := by
    simpa only [CartesianMonoidalCategory.lift_snd_fst] using
      (braidingData A B).2
  let baseBackward : X.right ⊗ (Y.right ⊗ Z.right) ⟶
      (X.right ⊗ Y.right) ⊗ Z.right :=
    (X.right ◁ (β_ Y.right Z.right).hom) ≫
      (β_ X.right (Z.right ⊗ Y.right)).hom ≫
      (α_ Z.right Y.right X.right).hom ≫
      (Z.right ◁ (β_ Y.right X.right).hom) ≫
      (β_ Z.right (X.right ⊗ Y.right)).hom
  have hBaseBackward : baseBackward =
      (α_ X.right Y.right Z.right).inv := by
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext <;>
        simp [baseBackward, Category.assoc]
    · simp [baseBackward, Category.assoc]
  have hMapYZ : q X (((smash P hP).obj Y).obj Z) ≫
        (((smash P hP).obj X).map (braidingData Y Z).1.hom).right =
      (𝟙 X.right ⊗ₘ (braidingData Y Z).1.hom.right) ≫
        q X (((smash P hP).obj Z).obj Y) := by
    exact smashMap_q X (braidingData Y Z).1.hom
  have hMapYX : q Z (((smash P hP).obj Y).obj X) ≫
        (((smash P hP).obj Z).map (braidingData Y X).1.hom).right =
      (𝟙 Z.right ⊗ₘ (braidingData Y X).1.hom.right) ≫
        q Z (((smash P hP).obj X).obj Y) := by
    exact smashMap_q Z (braidingData Y X).1.hom
  have hRoot1 : q X (((smash P hP).obj Z).obj Y) ≫
        (braidingData X (((smash P hP).obj Z).obj Y)).1.hom.right =
      (β_ X.right (((smash P hP).obj Z).obj Y).right).hom ≫
        q (((smash P hP).obj Z).obj Y) X :=
    braiding_q X (((smash P hP).obj Z).obj Y)
  have hRoot2 : q Z (((smash P hP).obj X).obj Y) ≫
        (braidingData Z (((smash P hP).obj X).obj Y)).1.hom.right =
      (β_ Z.right (((smash P hP).obj X).obj Y).right).hom ≫
        q (((smash P hP).obj X).obj Y) Z :=
    braiding_q Z (((smash P hP).obj X).obj Y)
  have hAssocZYX :
      ((q Z Y ▷ X.right) ≫ q (((smash P hP).obj Z).obj Y) X) ≫
          (assocHom Z Y X).1.right =
        (α_ Z.right Y.right X.right).hom ≫
          (Z.right ◁ q Y X) ≫ q Z (((smash P hP).obj Y).obj X) :=
    assocHom_q Z Y X
  dsimp only [backward, smashAssociatorBackwardMap]
  simp only [Under.comp_right]
  slice_lhs 2 3 => rw [hMapYZ]
  simp only [MonoidalCategory.id_tensorHom, Category.assoc]
  slice_lhs 1 2 =>
    rw [← MonoidalCategory.whiskerLeft_comp, braiding_q Y Z,
      MonoidalCategory.whiskerLeft_comp]
  slice_lhs 3 4 => rw [hRoot1]
  slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality_right]
  slice_lhs 3 5 => rw [← Category.assoc, hAssocZYX]
  slice_lhs 5 6 => rw [hMapYX]
  simp only [MonoidalCategory.id_tensorHom, Category.assoc]
  slice_lhs 4 5 =>
    rw [← MonoidalCategory.whiskerLeft_comp, braiding_q Y X,
      MonoidalCategory.whiskerLeft_comp]
  slice_lhs 6 7 => rw [hRoot2]
  slice_lhs 5 6 => rw [BraidedCategory.braiding_naturality_right]
  simpa only [baseBackward, Category.assoc] using congrArg
    (fun k => k ≫ (q X Y ▷ Z.right) ≫
      q (((smash P hP).obj X).obj Y) Z) hBaseBackward
set_option backward.isDefEq.respectTransparency false in
@[no_expose]
noncomputable def smashAssociatorData (X Y Z : Under P) :
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    { e : ((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z ≅
          ((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z) //
      (((q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) ≫
          e.hom.right =
        (α_ X.right Y.right Z.right).hom ≫
          (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ∧
      (((X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ≫
          e.inv.right =
        (α_ X.right Y.right Z.right).inv ≫
          (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) } := by
  let data :
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      { e : ((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z ≅
            ((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z) //
        (((q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) ≫
            e.hom.right =
          (α_ X.right Y.right Z.right).hom ≫
            (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ∧
        (((X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ≫
            e.inv.right =
          (α_ X.right Y.right Z.right).inv ≫
            (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) } := by
    let collapse (A B : Under P) :=
      hP.from (((wedge P).obj A).obj B).right
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    let b (A B : Under P) :
        P ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inr
    let leftFace (A B : Under P) :=
      CartesianMonoidalCategory.lift (𝟙 A.right)
        (hP.from A.right ≫ B.hom)
    let rightFace (A B : Under P) :=
      CartesianMonoidalCategory.lift
        (hP.from B.right ≫ A.hom) (𝟙 B.right)
    have hLeftFace (A B : Under P) :
        pushout.inl A.hom B.hom ≫
            (smashPresentation P hP A B).1.right =
          leftFace A B := by
      exact smashPresentation_wedge_inl P hP A B
    have hRightFace (A B : Under P) :
        pushout.inr A.hom B.hom ≫
            (smashPresentation P hP A B).1.right =
          rightFace A B := by
      exact smashPresentation_wedge_inr P hP A B
    have hQLeftMap (A B : Under P)
        {T : C} (f : T ⟶ A.right) :
        CartesianMonoidalCategory.lift f
            (hP.from T ≫ B.hom) ≫ q A B =
          hP.from T ≫ b A B := by
      exact smashQuotient_lift_left P hP A B f
    have hQRightMap (A B : Under P)
        {T : C} (f : T ⟶ B.right) :
        CartesianMonoidalCategory.lift
            (hP.from T ≫ A.hom) f ≫ q A B =
          hP.from T ≫ b A B := by
      exact smashQuotient_lift_right P hP A B f
    let assocHom := smashAssociatorForwardData P hP
    have assocHom_q (A B C : Under P) :
        ((q A B ▷ C.right) ≫ q (((smash P hP).obj A).obj B) C) ≫
            (assocHom A B C).1.right =
          (α_ A.right B.right C.right).hom ≫
            (A.right ◁ q B C) ≫ q A (((smash P hP).obj B).obj C) := by
      exact (assocHom A B C).2
    let forward := (assocHom X Y Z).1
    let backward := smashAssociatorBackwardMap P hP X Y Z
    have backward_q :
        ((X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ≫
            backward.right =
          (α_ X.right Y.right Z.right).inv ≫
            (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z := by
      exact smashAssociatorBackwardMap_quotient P hP X Y Z
    have hPL : IsPushout
        ((smashPresentation P hP X Y).1.right ▷ Z.right)
        (collapse X Y ▷ Z.right)
        (q X Y ▷ Z.right) (b X Y ▷ Z.right) := by
      exact Functor.map_isPushout (tensorRight Z.right)
        (IsPushout.of_isColimit_cocone
          (smashPresentation P hP X Y).2.2)
    have hPR : IsPushout
        (X.right ◁ (smashPresentation P hP Y Z).1.right)
        (X.right ◁ collapse Y Z)
        (X.right ◁ q Y Z) (X.right ◁ b Y Z) := by
      exact Functor.map_isPushout (tensorLeft X.right)
        (IsPushout.of_isColimit_cocone
          (smashPresentation P hP Y Z).2.2)
    have hQInnerRightBase : (b X Y ▷ Z.right) ≫
        q (((smash P hP).obj X).obj Y) Z =
          hP.from
            (P ⊗ Z.right) ≫
              b (((smash P hP).obj X).obj Y) Z := by
      have hfac : b X Y ▷ Z.right =
          CartesianMonoidalCategory.lift
            (hP.from
                (P ⊗ Z.right) ≫
              (((smash P hP).obj X).obj Y).hom)
            (CartesianMonoidalCategory.snd P Z.right) := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [CartesianMonoidalCategory.whiskerRight_fst,
            CartesianMonoidalCategory.lift_fst]
          have hp : CartesianMonoidalCategory.fst P Z.right =
              hP.from
                (P ⊗ Z.right) :=
            hP.hom_ext _ _
          change CartesianMonoidalCategory.fst P Z.right ≫
              b X Y =
            hP.from
                (P ⊗ Z.right) ≫ b X Y
          simpa only [Category.assoc] using congrArg
            (fun k : P ⊗ Z.right ⟶ P => k ≫ b X Y) hp
        · simp
      rw [hfac]
      exact hQRightMap (((smash P hP).obj X).obj Y) Z _
    have hQInnerLeftBase : (X.right ◁ b Y Z) ≫
        q X (((smash P hP).obj Y).obj Z) =
          hP.from
            (X.right ⊗ P) ≫
              b X (((smash P hP).obj Y).obj Z) := by
      have hfac : X.right ◁ b Y Z =
          CartesianMonoidalCategory.lift
            (CartesianMonoidalCategory.fst X.right P)
            (hP.from
                (X.right ⊗ P) ≫
              b Y Z) := by
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simp only [CartesianMonoidalCategory.lift_snd,
            CartesianMonoidalCategory.whiskerLeft_snd]
          simpa only [Category.assoc] using congrArg
            (fun k : X.right ⊗ P ⟶ P =>
              k ≫ b Y Z) (hP.hom_ext _ _)
      rw [hfac]
      exact hQLeftMap X (((smash P hP).obj Y).obj Z) _
    have hPointLeft : b (((smash P hP).obj X).obj Y) Z ≫ forward.right ≫
        backward.right = b (((smash P hP).obj X).obj Y) Z := by
      change (((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z).hom ≫
          forward.right ≫ backward.right =
        (((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z).hom
      simpa only [Under.comp_right, Category.assoc] using
        Under.w (forward ≫ backward)
    have hPointRight : b X (((smash P hP).obj Y).obj Z) ≫ backward.right ≫
        forward.right = b X (((smash P hP).obj Y).obj Z) := by
      change (((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z)).hom ≫
          backward.right ≫ forward.right =
        (((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z)).hom
      simpa only [Under.comp_right, Category.assoc] using
        Under.w (backward ≫ forward)
    refine ⟨{
        hom := forward
        inv := backward
        hom_inv_id := by
          apply Under.UnderMorphism.ext
          change forward.right ≫ backward.right =
            𝟙 (smashPresentation P hP
              (((smash P hP).obj X).obj Y) Z).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP
              (((smash P hP).obj X).obj Y) Z).2.2
          · apply hPL.hom_ext
            · slice_lhs 1 3 => rw [← Category.assoc, assocHom_q X Y Z]
              slice_lhs 2 4 => rw [← Category.assoc, backward_q]
              simp only [Iso.hom_inv_id_assoc]
              change (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z =
                (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z ≫ 𝟙 _
              rw [Category.comp_id]
            · slice_lhs 1 2 => rw [hQInnerRightBase]
              slice_lhs 2 4 => rw [hPointLeft]
              change hP.from
                    (P ⊗ Z.right) ≫
                    b (((smash P hP).obj X).obj Y) Z =
                (b X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z ≫ 𝟙 _
              rw [Category.comp_id, hQInnerRightBase]
          · change b (((smash P hP).obj X).obj Y) Z ≫ forward.right ≫
                backward.right = b (((smash P hP).obj X).obj Y) Z ≫ 𝟙 _
            rw [hPointLeft, Category.comp_id]
        inv_hom_id := by
          apply Under.UnderMorphism.ext
          change backward.right ≫ forward.right =
            𝟙 (smashPresentation P hP X
              (((smash P hP).obj Y).obj Z)).2.1.pt
          apply PushoutCocone.IsColimit.hom_ext
            (smashPresentation P hP X
              (((smash P hP).obj Y).obj Z)).2.2
          · apply hPR.hom_ext
            · slice_lhs 1 3 => rw [← Category.assoc, backward_q]
              slice_lhs 2 4 => rw [← Category.assoc, assocHom_q X Y Z]
              simp only [Iso.inv_hom_id_assoc]
              change (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z) =
                (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z) ≫ 𝟙 _
              rw [Category.comp_id]
            · slice_lhs 1 2 => rw [hQInnerLeftBase]
              slice_lhs 2 4 => rw [hPointRight]
              change hP.from
                    (X.right ⊗ P) ≫
                    b X (((smash P hP).obj Y).obj Z) =
                (X.right ◁ b Y Z) ≫ q X (((smash P hP).obj Y).obj Z) ≫ 𝟙 _
              rw [Category.comp_id, hQInnerLeftBase]
          · change b X (((smash P hP).obj Y).obj Z) ≫ backward.right ≫
                forward.right = b X (((smash P hP).obj Y).obj Z) ≫ 𝟙 _
            rw [hPointRight, Category.comp_id] }, ?_, ?_⟩
    · exact assocHom_q X Y Z
    · exact backward_q
  exact data


/-- The selected associator data uses the named forward map. -/
public theorem smashAssociatorData_hom (X Y Z : Under P) :
    (smashAssociatorData P hP X Y Z).1.hom =
      (smashAssociatorForwardData P hP X Y Z).1 := by
  rfl

/-- The selected associator data uses the named reverse map. -/
public theorem smashAssociatorData_inv (X Y Z : Under P) :
    (smashAssociatorData P hP X Y Z).1.inv =
      smashAssociatorBackwardMap P hP X Y Z := by
  rfl

/-- The associator for the generic smash product. -/
noncomputable def smashAssociator (X Y Z : Under P) :
    ((smash P hP).obj (((smash P hP).obj X).obj Y)).obj Z ≅
      ((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z) :=
  (smashAssociatorData P hP X Y Z).1

/-- The smash associator carries the left-associated two-stage quotient
through the ambient associator. -/
theorem smashAssociator_hom_quotient (X Y Z : Under P) :
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    ((q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z) ≫
        (smashAssociator P hP X Y Z).hom.right =
      (α_ X.right Y.right Z.right).hom ≫
        (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z) := by
  exact (smashAssociatorData P hP X Y Z).2.1

/-- The inverse smash associator carries the right-associated two-stage
quotient through the inverse ambient associator. -/
theorem smashAssociator_inv_quotient (X Y Z : Under P) :
    let q (A B : Under P) :
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
      (smashPresentation P hP A B).2.1.inl
    ((X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)) ≫
        (smashAssociator P hP X Y Z).inv.right =
      (α_ X.right Y.right Z.right).inv ≫
        (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z := by
  exact (smashAssociatorData P hP X Y Z).2.2

set_option linter.unusedSectionVars false in
private theorem smashMonoidalTensorLaws :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    (∀ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B'),
      (smashPresentation P hP A B).2.1.inl ≫ (μ f g).right =
        (f.right ⊗ₘ g.right) ≫
          (smashPresentation P hP A' B').2.1.inl) ∧
    (∀ A B : Under P, Epi (smashPresentation P hP A B).2.1.inl) ∧
    (∀ (A B : Under P) (T : C),
      Epi ((smashPresentation P hP A B).2.1.inl ▷ T)) ∧
    (∀ (A B : Under P) (T U : C),
      Epi (((smashPresentation P hP A B).2.1.inl ▷ T) ▷ U)) ∧
    (∀ {X₁ Y₁ X₂ Y₂ : Under P} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      μ f g = μ f (𝟙 X₂) ≫ μ (𝟙 Y₁) g) ∧
    (∀ X Y : Under P,
      μ (𝟙 X) (𝟙 Y) = 𝟙 (((smash P hP).obj X).obj Y)) ∧
    (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Under P}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
      μ f₁ f₂ ≫ μ g₁ g₂ = μ (f₁ ≫ g₁) (f₂ ≫ g₂)) := by
  dsimp only
  let μ (P : C) (hP : IsTerminal P) {A A' B B' : Under P}
      (f : A ⟶ A') (g : B ⟶ B') :=
    ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
  have map_q {P : C} (hP : IsTerminal P)
      {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :
      (smashPresentation P hP A B).2.1.inl ≫ (μ P hP f g).right =
        (f.right ⊗ₘ g.right) ≫
          (smashPresentation P hP A' B').2.1.inl := by
    set_option backward.isDefEq.respectTransparency false in
      let data := smashMapData
      have map_first := data.2.2 P hP f B
      have map_second_q :
          (smashPresentation P hP A' B).2.1.inl ≫
              (((smash P hP).obj A').map g).right =
            (𝟙 A'.right ⊗ₘ g.right) ≫
              (smashPresentation P hP A' B').2.1.inl := by
        unfold smash
        exact PushoutCocone.IsColimit.inl_desc
          (smashPresentation P hP A' B).2.2 _ _ _
      dsimp only [μ]
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [← map_first, data.2.1 hP f (𝟙 B)]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id,
        Category.assoc]
      slice_lhs 2 3 => rw [map_second_q]
      simp only [MonoidalCategory.id_tensorHom]
      slice_lhs 1 2 => rw [← MonoidalCategory.tensorHom_def]
  have epiData := smashEpiData P hP
  have epiQ := epiData.1
  have epiQR := epiData.2.1
  have epiQRR (A B : Under P) (T U : C) :
      Epi (((smashPresentation P hP A B).2.1.inl ▷ T) ▷ U) :=
    smashDoubleWhiskerEpi P hP A B T U
  have identityTensor (X Y : Under P) :
      μ P hP (𝟙 X) (𝟙 Y) = 𝟙 (((smash P hP).obj X).obj Y) := by
    dsimp only [μ]
    simp
  have tensorComposition
      {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Under P}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
      μ P hP f₁ f₂ ≫ μ P hP g₁ g₂ =
        μ P hP (f₁ ≫ g₁) (f₂ ≫ g₂) :=
    smashTensorHomComposition P hP (fun f g => μ P hP f g)
      (fun f g => map_q hP f g) epiQ f₁ f₂ g₁ g₂
  have tensorHomDef
      {X₁ Y₁ X₂ Y₂ : Under P} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
      μ P hP f g =
        μ P hP f (𝟙 X₂) ≫ μ P hP (𝟙 Y₁) g := by
    simpa using (tensorComposition f (𝟙 X₂) (𝟙 Y₁) g).symm
  exact ⟨map_q hP, ⟨epiQ, ⟨epiQR, ⟨epiQRR, ⟨tensorHomDef,
    ⟨identityTensor, tensorComposition⟩⟩⟩⟩⟩⟩
where
  smashMapData :
      { smashMap :
        ∀ (P : C) (hP : IsTerminal P) {A A' B B' : Under P},
          (A ⟶ A') → (B ⟶ B') →
            (((smash P hP).obj A).obj B ⟶
              ((smash P hP).obj A').obj B') //
        (∀ {P : C} (hP : IsTerminal P) {A A' B B' : Under P}
          (f : A ⟶ A') (g : B ⟶ B'),
          (smashPresentation P hP A B).2.1.inl ≫
              (smashMap P hP f g).right =
            (f.right ⊗ₘ g.right) ≫
              (smashPresentation P hP A' B').2.1.inl) ∧
        (∀ (P : C) (hP : IsTerminal P) {A A' : Under P}
          (f : A ⟶ A') (B : Under P),
          smashMap P hP f (𝟙 B) = ((smash P hP).map f).app B) } := by
    set_option backward.isDefEq.respectTransparency false in
      let smashPushout (P : C) (hP : IsTerminal P)
          (X Y : Under P) : Under P :=
        Under.mk
          (show P ⟶ (smashPresentation P hP X Y).2.1.pt from
            (smashPresentation P hP X Y).2.1.inr)
      let smashMap (P : C) (hP : IsTerminal P)
          {X X' Y Y' : Under P}
          (f : X ⟶ X') (g : Y ⟶ Y') :
          smashPushout P hP X Y ⟶ smashPushout P hP X' Y' := by
        let p := smashPresentation P hP X Y
        let p' := smashPresentation P hP X' Y'
        let wedgeMap : ((wedge P).obj X).obj Y ⟶
            ((wedge P).obj X').obj Y' :=
          Under.homMk
            (pushout.map X.hom Y.hom X'.hom Y'.hom f.right g.right
              (𝟙 P)
              (by simpa only [Category.id_comp] using Under.w f)
              (by simpa only [Category.id_comp] using Under.w g)) (by
                dsimp [wedge]
                rw [Category.assoc, pushout.inl_desc,
                  ← Category.assoc, Under.w f])
        have hProd : p.1.right ≫ (f.right ⊗ₘ g.right) =
            wedgeMap.right ≫ p'.1.right := by
          dsimp only [p, p', smashPresentation]
          dsimp only [wedgeMap, Under.homMk_right]
          apply pushout.hom_ext
          · apply CartesianMonoidalCategory.hom_ext
            · simp [Category.assoc]
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.id_comp, Category.assoc,
                Under.w, CartesianMonoidalCategory.lift_snd, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from X.right)
                  (f.right ≫ hP.from X'.right)]
          · apply CartesianMonoidalCategory.hom_ext
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.assoc, Under.w,
                Category.id_comp, CartesianMonoidalCategory.lift_fst, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from Y.right)
                  (g.right ≫ hP.from Y'.right)]
            · simp [Category.assoc]
        have hPoint : wedgeMap.right ≫
            hP.from (((wedge P).obj X').obj Y').right =
          hP.from (((wedge P).obj X).obj Y).right :=
          hP.hom_ext _ _
        have hCompat : p.1.right ≫
              ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl) =
            hP.from (((wedge P).obj X).obj Y).right ≫ p'.2.1.inr := by
          rw [← Category.assoc, hProd, Category.assoc, p'.2.1.condition]
          rw [← Category.assoc, hPoint]
        let t : PushoutCocone p.1.right
            (hP.from (((wedge P).obj X).obj Y).right) :=
          PushoutCocone.mk
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr hCompat
        exact Under.homMk
          (PushoutCocone.IsColimit.desc p.2.2 t.inl t.inr t.condition) (by
          exact PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
      have map_q {P : C} (hP : IsTerminal P)
          {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :
          (smashPresentation P hP A B).2.1.inl ≫
              (smashMap P hP f g).right =
            (f.right ⊗ₘ g.right) ≫
              (smashPresentation P hP A' B').2.1.inl := by
        let p := smashPresentation P hP A B
        let p' := smashPresentation P hP A' B'
        change p.2.1.inl ≫ PushoutCocone.IsColimit.desc p.2.2
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr _ =
          (f.right ⊗ₘ g.right) ≫ p'.2.1.inl
        exact PushoutCocone.IsColimit.inl_desc p.2.2 _ _ _
      have map_first (P : C) (hP : IsTerminal P)
          {A A' : Under P} (f : A ⟶ A') (B : Under P) :
          smashMap P hP f (𝟙 B) = ((smash P hP).map f).app B := by
        rfl
      exact ⟨smashMap, map_q, map_first⟩
  -- Epimorphism properties of the same smash quotient.
  smashEpiData (P : C) (hP : IsTerminal P) :
      (∀ X Y : Under P,
        Epi (smashPresentation P hP X Y).2.1.inl) ∧
      (∀ (X Y : Under P) (T : C),
        Epi ((smashPresentation P hP X Y).2.1.inl ▷ T)) ∧
      (∀ (T : C) (X Y : Under P),
        Epi (T ◁ (smashPresentation P hP X Y).2.1.inl)) := by
    set_option backward.isDefEq.respectTransparency false in
      have epi_right_of_isPushout_of_splitEpi
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (h : IsPushout t l r b) (s : X ⟶ A)
          (hs : s ≫ l = 𝟙 X) : Epi r := by
        constructor
        intro Z f g hr
        apply h.hom_ext
        · exact hr
        · calc
            b ≫ f = (𝟙 X) ≫ b ≫ f := by simp
            _ = (s ≫ l) ≫ b ≫ f := by rw [hs]
            _ = s ≫ (l ≫ b) ≫ f := by simp only [Category.assoc]
            _ = s ≫ (t ≫ r) ≫ f := by rw [h.w]
            _ = s ≫ t ≫ (r ≫ f) := by simp only [Category.assoc]
            _ = s ≫ t ≫ (r ≫ g) := by rw [hr]
            _ = s ≫ (t ≫ r) ≫ g := by simp only [Category.assoc]
            _ = s ≫ (l ≫ b) ≫ g := by rw [h.w]
            _ = (s ≫ l) ≫ b ≫ g := by simp only [Category.assoc]
            _ = b ≫ g := by rw [hs]; simp
      have map_isPushout_of_preserves
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (F : C ⥤ C) [PreservesColimit (span t l) F]
          (h : IsPushout t l r b) :
          IsPushout (F.map t) (F.map l) (F.map r) (F.map b) :=
        IsPushout.of_isColimit_cocone
          (PreservesColimit.preserves h.isColimit).some
      have map_epi_right_of_isPushout_of_splitEpi
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (F : C ⥤ C) [PreservesColimit (span t l) F]
          (h : IsPushout t l r b) (s : X ⟶ A)
          (hs : s ≫ l = 𝟙 X) : Epi (F.map r) := by
        apply epi_right_of_isPushout_of_splitEpi
          (map_isPushout_of_preserves F h) (F.map s)
        rw [← F.map_comp, hs, F.map_id]
      -- The same quotient map is an epimorphism.
      have smashQuotient_epi (P : C) (hP : IsTerminal P)
          (X Y : Under P) :
          Epi ((smashPresentation P hP X Y).2.1.inl) := by
        let W := ((wedge P).obj X).obj Y
        let c : W.right ⟶ P := hP.from W.right
        have hs : W.hom ≫ c = 𝟙 P := hP.hom_ext _ _
        exact epi_right_of_isPushout_of_splitEpi
          (IsPushout.of_isColimit_cocone
            (smashPresentation P hP X Y).2.2)
          W.hom hs
      have smashQuotient_whiskerRight_epi (P : C) (hP : IsTerminal P)
          (X Y : Under P) (T : C) :
          Epi ((smashPresentation P hP X Y).2.1.inl ▷ T) := by
        let W := ((wedge P).obj X).obj Y
        let c : W.right ⟶ P := hP.from W.right
        have hs : W.hom ≫ c = 𝟙 P := hP.hom_ext _ _
        exact map_epi_right_of_isPushout_of_splitEpi (tensorRight T)
          (IsPushout.of_isColimit_cocone
            (smashPresentation P hP X Y).2.2)
          W.hom hs
      have smashQuotient_whiskerLeft_epi (P : C) (hP : IsTerminal P)
          (T : C) (X Y : Under P) :
          Epi (T ◁ (smashPresentation P hP X Y).2.1.inl) := by
        let W := ((wedge P).obj X).obj Y
        let c : W.right ⟶ P := hP.from W.right
        have hs : W.hom ≫ c = 𝟙 P := hP.hom_ext _ _
        exact map_epi_right_of_isPushout_of_splitEpi (tensorLeft T)
          (IsPushout.of_isColimit_cocone
            (smashPresentation P hP X Y).2.2)
          W.hom hs
      exact ⟨smashQuotient_epi P hP,
        smashQuotient_whiskerRight_epi P hP,
        smashQuotient_whiskerLeft_epi P hP⟩
  -- Both whiskerings preserve the quotient epimorphism.
  smashDoubleWhiskerEpi (P : C)
      (hP : IsTerminal P) (W X : Under P) (Y Z : C) :
      Epi (((smashPresentation P hP W X).2.1.inl ▷ Y) ▷ Z) := by
    set_option backward.isDefEq.respectTransparency false in
      have epi_right_of_isPushout_of_splitEpi
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (h : IsPushout t l r b) (s : X ⟶ A)
          (hs : s ≫ l = 𝟙 X) : Epi r := by
        constructor
        intro Z f g hr
        apply h.hom_ext
        · exact hr
        · calc
            b ≫ f = (𝟙 X) ≫ b ≫ f := by simp
            _ = (s ≫ l) ≫ b ≫ f := by rw [hs]
            _ = s ≫ (l ≫ b) ≫ f := by simp only [Category.assoc]
            _ = s ≫ (t ≫ r) ≫ f := by rw [h.w]
            _ = s ≫ t ≫ (r ≫ f) := by simp only [Category.assoc]
            _ = s ≫ t ≫ (r ≫ g) := by rw [hr]
            _ = s ≫ (t ≫ r) ≫ g := by simp only [Category.assoc]
            _ = s ≫ (l ≫ b) ≫ g := by rw [h.w]
            _ = (s ≫ l) ≫ b ≫ g := by simp only [Category.assoc]
            _ = b ≫ g := by rw [hs]; simp
      have map_isPushout_of_preserves
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (F : C ⥤ C) [PreservesColimit (span t l) F]
          (h : IsPushout t l r b) :
          IsPushout (F.map t) (F.map l) (F.map r) (F.map b) :=
        IsPushout.of_isColimit_cocone
          (PreservesColimit.preserves h.isColimit).some
      have map_epi_right_of_isPushout_of_splitEpi
          {A B X Y : C} {t : A ⟶ B} {l : A ⟶ X}
          {r : B ⟶ Y} {b : X ⟶ Y}
          (F : C ⥤ C) [PreservesColimit (span t l) F]
          (h : IsPushout t l r b) (s : X ⟶ A)
          (hs : s ≫ l = 𝟙 X) : Epi (F.map r) := by
        apply epi_right_of_isPushout_of_splitEpi
          (map_isPushout_of_preserves F h) (F.map s)
        rw [← F.map_comp, hs, F.map_id]
      let F := tensorRight Y ⋙ tensorRight Z
      let V := ((wedge P).obj W).obj X
      let collapse := hP.from V.right
      have hs : V.hom ≫ collapse = 𝟙 P := hP.hom_ext _ _
      change Epi (F.map (smashPresentation P hP W X).2.1.inl)
      exact map_epi_right_of_isPushout_of_splitEpi F
        (IsPushout.of_isColimit_cocone
          (smashPresentation P hP W X).2.2) V.hom hs
  -- The smash tensor maps preserve composition.
  smashTensorHomComposition
      (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (map_q : ∀ {A A' B B' : Under P}
        (f : A ⟶ A') (g : B ⟶ B'),
        (smashPresentation P hP A B).2.1.inl ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫
            (smashPresentation P hP A' B').2.1.inl)
      (epiQ : ∀ A B : Under P,
        Epi (smashPresentation P hP A B).2.1.inl)
      {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Under P}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
      smashMap f₁ f₂ ≫ smashMap g₁ g₂ =
        smashMap (f₁ ≫ g₁) (f₂ ≫ g₂) := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      apply Under.UnderMorphism.ext
      let _ : Epi (q X₁ X₂) := epiQ X₁ X₂
      apply (cancel_epi (q X₁ X₂)).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [map_q f₁ f₂]
      simp only [Category.assoc]
      slice_lhs 2 3 => rw [map_q g₁ g₂]
      slice_rhs 1 2 => rw [map_q (f₁ ≫ g₁) (f₂ ≫ g₂)]
      slice_lhs 1 2 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [Under.comp_right]


private theorem smashMonoidalUnitCore :
    (∀ A B : Under P,
      (smashPresentation P hP A B).2.1.inl ≫
          (smashBraiding P hP A B).hom.right =
        (β_ A.right B.right).hom ≫
          (smashPresentation P hP B A).2.1.inl) ∧
    (∀ X Y : Under P,
      (α_ X.right (smashUnit P).right Y.right).hom ≫
            X.right ◁
              ((smashPresentation P hP (smashUnit P) Y).2.1.inl ≫
                (smashLeftUnitor P hP Y).hom.right) ≫
          (smashPresentation P hP X Y).2.1.inl =
        ((smashPresentation P hP X (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP X).hom.right) ▷ Y.right ≫
          (smashPresentation P hP X Y).2.1.inl) := by
  have braid_q (A B : Under P) :
      (smashPresentation P hP A B).2.1.inl ≫
          (smashBraiding P hP A B).hom.right =
        (β_ A.right B.right).hom ≫
          (smashPresentation P hP B A).2.1.inl := by
    set_option backward.isDefEq.respectTransparency false in
      let data := smashBraidingPacket P hP A B
      rw [data.2]
      simpa only [CartesianMonoidalCategory.lift_snd_fst] using data.1.2
  have leftData := smashLeftUnitorFormulas P hP
  have rightData := smashRightUnitorFormulas
    (fun P hP X Y => (smashBraidingPacket P hP X Y).1)
    (fun P hP A B => (smashBraidingPacket P hP A B).2)
    (fun P hP => (smashLeftUnitorFormulas P hP).1)
    (fun P hP => (smashLeftUnitorFormulas P hP).2) P hP
  have axisData := smashQAxisData P hP
  have core (X Y : Under P) := smashTriangleCore P hP X Y
    (leftData.1 Y) (leftData.2 Y) (rightData.1 X) (rightData.2 X)
    axisData.1 axisData.2
  exact ⟨braid_q, core⟩
where
  smashBraidingPacket (P : C) (hP : IsTerminal P)
      (X Y : Under P) :
      { d :
          { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
            (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
              CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.snd X.right Y.right)
                  (CartesianMonoidalCategory.fst X.right Y.right) ≫
                (smashPresentation P hP Y X).2.1.inl } //
        smashBraiding P hP X Y = d.1 } := by
    set_option backward.isDefEq.respectTransparency false in
      unfold smash
      let pointedProduct (P : C) : Under P ⥤ Under P ⥤ Under P :=
        { obj X :=
            { obj Y := Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
              map {Y Y'} g := Under.homMk (𝟙 X.right ⊗ₘ g.right) (by
                dsimp
                rw [CartesianMonoidalCategory.lift_map]
                simp only [Category.comp_id, Under.w])
              map_id Y := by
                apply Under.UnderMorphism.ext
                change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
                exact MonoidalCategory.id_tensorHom_id _ _
              map_comp g h := by
                apply Under.UnderMorphism.ext
                change (𝟙 X.right ⊗ₘ (g.right ≫ h.right)) =
                  (𝟙 X.right ⊗ₘ g.right) ≫ (𝟙 X.right ⊗ₘ h.right)
                rw [tensorHom_comp_tensorHom, Category.id_comp] }
          map {X X'} f :=
            { app Y := Under.homMk (f.right ⊗ₘ 𝟙 Y.right) (by
                dsimp
                rw [CartesianMonoidalCategory.lift_map]
                simp only [Category.comp_id, Under.w])
              naturality {Y Y'} g := by
                apply Under.UnderMorphism.ext
                change (𝟙 X.right ⊗ₘ g.right) ≫
                    (f.right ⊗ₘ 𝟙 Y'.right) =
                  (f.right ⊗ₘ 𝟙 Y.right) ≫
                    (𝟙 X'.right ⊗ₘ g.right)
                rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
                simp }
          map_id X := by
            apply NatTrans.ext
            funext Y
            apply Under.UnderMorphism.ext
            change (𝟙 X.right ⊗ₘ 𝟙 Y.right) = 𝟙 _
            exact MonoidalCategory.id_tensorHom_id _ _
          map_comp f g := by
            apply NatTrans.ext
            funext Y
            apply Under.UnderMorphism.ext
            change ((f.right ≫ g.right) ⊗ₘ 𝟙 Y.right) =
              (f.right ⊗ₘ 𝟙 Y.right) ≫ (g.right ⊗ₘ 𝟙 Y.right)
            rw [tensorHom_comp_tensorHom, Category.id_comp] }
      let wedgeToProduct (P : C) (hP : IsTerminal P) (X Y : Under P) :
          ((wedge P).obj X).obj Y ⟶ ((pointedProduct P).obj X).obj Y := by
        change Under.mk (X.hom ≫ pushout.inl X.hom Y.hom) ⟶
          Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom)
        let leftFace : X ⟶
              Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
            Under.homMk
              (CartesianMonoidalCategory.lift (𝟙 X.right)
                (hP.from X.right ≫ Y.hom)) (by
                  apply CartesianMonoidalCategory.hom_ext
                  · simp
                  · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
                    rw [← Category.assoc,
                      hP.hom_ext (X.hom ≫ hP.from X.right) (𝟙 P)]
                    simp)
        let rightFace : Y ⟶
              Under.mk (CartesianMonoidalCategory.lift X.hom Y.hom) :=
            Under.homMk
              (CartesianMonoidalCategory.lift
                (hP.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
                  apply CartesianMonoidalCategory.hom_ext
                  · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
                    rw [← Category.assoc,
                      hP.hom_ext (Y.hom ≫ hP.from Y.right) (𝟙 P)]
                    simp
                  · simp)
        exact Under.homMk
          (pushout.desc leftFace.right rightFace.right (by
            exact (Under.w leftFace).trans (Under.w rightFace).symm)) (by
              change (X.hom ≫ pushout.inl X.hom Y.hom) ≫
                  pushout.desc leftFace.right rightFace.right _ =
                CartesianMonoidalCategory.lift X.hom Y.hom
              rw [Category.assoc, pushout.inl_desc]
              exact Under.w leftFace)
      let data :
          { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
            (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
              CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.snd X.right Y.right)
                  (CartesianMonoidalCategory.fst X.right Y.right) ≫
                (smashPresentation P hP Y X).2.1.inl } := by
        let swapMap (A B : Under P) :
            { f : ((smash P hP).obj A).obj B ⟶
                ((smash P hP).obj B).obj A //
              (smashPresentation P hP A B).2.1.inl ≫ f.right =
                  (β_ A.right B.right).hom ≫
                    (smashPresentation P hP B A).2.1.inl ∧
                (smashPresentation P hP A B).2.1.inr ≫ f.right =
                  (smashPresentation P hP B A).2.1.inr } := by
          let pAB := smashPresentation P hP A B
          let pBA := smashPresentation P hP B A
          let wedgeSwap : ((wedge P).obj A).obj B ⟶ ((wedge P).obj B).obj A :=
            Under.homMk (pushoutSymmetry A.hom B.hom).hom (by
              dsimp [wedge]
              rw [Category.assoc, inl_comp_pushoutSymmetry_hom]
              exact pushout.condition.symm)
          let productSwap : ((pointedProduct P).obj A).obj B ⟶
              ((pointedProduct P).obj B).obj A :=
            Under.homMk (β_ A.right B.right).hom (by
              dsimp [pointedProduct]
              apply CartesianMonoidalCategory.hom_ext <;> simp)
          have hProd : pAB.1.right ≫ productSwap.right =
              wedgeSwap.right ≫ pBA.1.right := by
            dsimp only [pAB, pBA, smashPresentation]
            change pushout.desc _ _ _ ≫ (β_ A.right B.right).hom =
              (pushoutSymmetry A.hom B.hom).hom ≫ pushout.desc _ _ _
            apply pushout.hom_ext
            · rw [← Category.assoc, pushout.inl_desc]
              rw [← Category.assoc]
              simp only [inl_comp_pushoutSymmetry_hom, pushout.inr_desc]
              apply CartesianMonoidalCategory.hom_ext <;> simp
            · rw [← Category.assoc, pushout.inr_desc]
              rw [← Category.assoc]
              simp only [inr_comp_pushoutSymmetry_hom, pushout.inl_desc]
              apply CartesianMonoidalCategory.hom_ext <;> simp
          have hPoint : hP.from
                (((wedge P).obj A).obj B).right ≫ 𝟙 P =
              wedgeSwap.right ≫ hP.from
                (((wedge P).obj B).obj A).right :=
            hP.hom_ext _ _
          have hCompat : pAB.1.right ≫
                (productSwap.right ≫ pBA.2.1.inl) =
              hP.from (((wedge P).obj A).obj B).right ≫ pBA.2.1.inr := by
            rw [← Category.assoc, hProd, Category.assoc,
              pBA.2.1.condition, ← Category.assoc]
            simpa only [Category.assoc, Category.comp_id] using
              congrArg (fun k => k ≫ pBA.2.1.inr) hPoint.symm
          let f : ((smash P hP).obj A).obj B ⟶
              ((smash P hP).obj B).obj A := Under.homMk
            (PushoutCocone.IsColimit.desc pAB.2.2
              (productSwap.right ≫ pBA.2.1.inl) pBA.2.1.inr hCompat) (by
                exact PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _)
          exact ⟨f, PushoutCocone.IsColimit.inl_desc pAB.2.2 _ _ _,
            PushoutCocone.IsColimit.inr_desc pAB.2.2 _ _ _⟩
        refine ⟨{
            hom := (swapMap X Y).1
            inv := (swapMap Y X).1
            hom_inv_id := by
              apply Under.UnderMorphism.ext
              change (swapMap X Y).1.right ≫ (swapMap Y X).1.right =
                𝟙 (smashPresentation P hP X Y).2.1.pt
              apply PushoutCocone.IsColimit.hom_ext
                (smashPresentation P hP X Y).2.2
              · rw [← Category.assoc, (swapMap X Y).2.1,
                  Category.assoc, (swapMap Y X).2.1]
                simp
              · rw [← Category.assoc, (swapMap X Y).2.2,
                  (swapMap Y X).2.2]
                change (smashPresentation P hP X Y).2.1.inr =
                  (smashPresentation P hP X Y).2.1.inr ≫
                    𝟙 (smashPresentation P hP X Y).2.1.pt
                rw [Category.comp_id]
            inv_hom_id := by
              apply Under.UnderMorphism.ext
              change (swapMap Y X).1.right ≫ (swapMap X Y).1.right =
                𝟙 (smashPresentation P hP Y X).2.1.pt
              apply PushoutCocone.IsColimit.hom_ext
                (smashPresentation P hP Y X).2.2
              · rw [← Category.assoc, (swapMap Y X).2.1,
                  Category.assoc, (swapMap X Y).2.1]
                simp
              · rw [← Category.assoc, (swapMap Y X).2.2,
                  (swapMap X Y).2.2]
                change (smashPresentation P hP Y X).2.1.inr =
                  (smashPresentation P hP Y X).2.1.inr ≫
                    𝟙 (smashPresentation P hP Y X).2.1.pt
                rw [Category.comp_id]
            }, ?_⟩
        rw [(swapMap X Y).2.1,
          CartesianMonoidalCategory.lift_snd_fst]
      exact ⟨data, by unfold smashBraiding; rfl⟩
  smashQAxisData (P : C) (hP : IsTerminal P) :
      (∀ (A B : Under P) {T : C} (f : T ⟶ A.right),
        CartesianMonoidalCategory.lift f (hP.from T ≫ B.hom) ≫
            (smashPresentation P hP A B).2.1.inl =
          hP.from T ≫ (smashPresentation P hP A B).2.1.inr) ∧
      (∀ (A B : Under P) {T : C} (f : T ⟶ B.right),
        CartesianMonoidalCategory.lift (hP.from T ≫ A.hom) f ≫
            (smashPresentation P hP A B).2.1.inl =
          hP.from T ≫ (smashPresentation P hP A B).2.1.inr) := by
    set_option backward.isDefEq.respectTransparency false in
      let collapse (A B : Under P) :=
        hP.from (((wedge P).obj A).obj B).right
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      let b (A B : Under P) :
          P ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inr
      let leftFace (A B : Under P) :=
        CartesianMonoidalCategory.lift (𝟙 A.right)
          (hP.from A.right ≫ B.hom)
      let rightFace (A B : Under P) :=
        CartesianMonoidalCategory.lift
          (hP.from B.right ≫ A.hom) (𝟙 B.right)
      have hLeftFace (A B : Under P) :
          pushout.inl A.hom B.hom ≫
              (smashPresentation P hP A B).1.right =
            leftFace A B := by
        dsimp only [smashPresentation]
        change pushout.inl A.hom B.hom ≫ pushout.desc _ _ _ = _
        rw [pushout.inl_desc]
        rfl
      have hRightFace (A B : Under P) :
          pushout.inr A.hom B.hom ≫
              (smashPresentation P hP A B).1.right =
            rightFace A B := by
        dsimp only [smashPresentation]
        change pushout.inr A.hom B.hom ≫ pushout.desc _ _ _ = _
        rw [pushout.inr_desc]
        rfl
      have hQLeft (A B : Under P) :
          leftFace A B ≫ q A B =
            hP.from A.right ≫ b A B := by
        rw [← hLeftFace A B, Category.assoc,
          (smashPresentation P hP A B).2.1.condition]
        have hp : pushout.inl A.hom B.hom ≫ collapse A B =
            hP.from A.right :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using congrArg
          (fun k : A.right ⟶ P => k ≫ b A B) hp
      have hQRight (A B : Under P) :
          rightFace A B ≫ q A B =
            hP.from B.right ≫ b A B := by
        rw [← hRightFace A B, Category.assoc,
          (smashPresentation P hP A B).2.1.condition]
        have hp : pushout.inr A.hom B.hom ≫ collapse A B =
            hP.from B.right :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using congrArg
          (fun k : B.right ⟶ P => k ≫ b A B) hp
      have hQLeftMap (A B : Under P)
          {T : C} (f : T ⟶ A.right) :
          CartesianMonoidalCategory.lift f
              (hP.from T ≫ B.hom) ≫ q A B =
            hP.from T ≫ b A B := by
        have hfac : CartesianMonoidalCategory.lift f
              (hP.from T ≫ B.hom) =
            f ≫ leftFace A B := by
          apply CartesianMonoidalCategory.hom_ext
          · simp [leftFace]
          · simp only [leftFace, Category.assoc,
              CartesianMonoidalCategory.lift_snd]
            have hp : hP.from T =
                f ≫ hP.from A.right :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : T ⟶ P => k ≫ B.hom) hp
        rw [hfac, Category.assoc, hQLeft]
        have hp : f ≫ hP.from A.right =
            hP.from T :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun k : T ⟶ P => k ≫ b A B) hp
      have hQRightMap (A B : Under P)
          {T : C} (f : T ⟶ B.right) :
          CartesianMonoidalCategory.lift
              (hP.from T ≫ A.hom) f ≫ q A B =
            hP.from T ≫ b A B := by
        have hfac : CartesianMonoidalCategory.lift
              (hP.from T ≫ A.hom) f =
            f ≫ rightFace A B := by
          apply CartesianMonoidalCategory.hom_ext
          · simp only [rightFace, Category.assoc,
              CartesianMonoidalCategory.lift_fst]
            have hp : hP.from T =
                f ≫ hP.from B.right :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using
              congrArg (fun k : T ⟶ P => k ≫ A.hom) hp
          · simp [rightFace]
        rw [hfac, Category.assoc, hQRight]
        have hp : f ≫ hP.from B.right =
            hP.from T :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using
          congrArg (fun k : T ⟶ P => k ≫ b A B) hp
      exact ⟨hQLeftMap, hQRightMap⟩
  -- The left unitor retains the quotient formulas.
  smashLeftUnitorFormulas (P : C)
      (hP : IsTerminal P) :
      (∀ T : Under P,
        ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          hP.from (P ⊗ T.right) ≫ T.hom) ∧
      (∀ T : Under P,
        ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          ((hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ T.right) ≫
            (λ_ T.right).hom) := by
    set_option backward.isDefEq.respectTransparency false in
      let smashPushout (P : C) (hP : IsTerminal P)
          (X Y : Under P) : Under P :=
        Under.mk
          (show P ⟶ (smashPresentation P hP X Y).2.1.pt from
            (smashPresentation P hP X Y).2.1.inr)
      let smashMap (P : C) (hP : IsTerminal P)
          {X X' Y Y' : Under P}
          (f : X ⟶ X') (g : Y ⟶ Y') :
          smashPushout P hP X Y ⟶ smashPushout P hP X' Y' := by
        let p := smashPresentation P hP X Y
        let p' := smashPresentation P hP X' Y'
        let wedgeMap : ((wedge P).obj X).obj Y ⟶
            ((wedge P).obj X').obj Y' :=
          Under.homMk
            (pushout.map X.hom Y.hom X'.hom Y'.hom f.right g.right
              (𝟙 P)
              (by simpa only [Category.id_comp] using Under.w f)
              (by simpa only [Category.id_comp] using Under.w g)) (by
                dsimp [wedge]
                rw [Category.assoc, pushout.inl_desc,
                  ← Category.assoc, Under.w f])
        have hProd : p.1.right ≫ (f.right ⊗ₘ g.right) =
            wedgeMap.right ≫ p'.1.right := by
          dsimp only [p, p', smashPresentation]
          dsimp only [wedgeMap, Under.homMk_right]
          apply pushout.hom_ext
          · apply CartesianMonoidalCategory.hom_ext
            · simp [Category.assoc]
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.id_comp, Category.assoc,
                Under.w, CartesianMonoidalCategory.lift_snd, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from X.right)
                  (f.right ≫ hP.from X'.right)]
          · apply CartesianMonoidalCategory.hom_ext
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.assoc, Under.w,
                Category.id_comp, CartesianMonoidalCategory.lift_fst, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from Y.right)
                  (g.right ≫ hP.from Y'.right)]
            · simp [Category.assoc]
        have hPoint : wedgeMap.right ≫
            hP.from (((wedge P).obj X').obj Y').right =
          hP.from (((wedge P).obj X).obj Y).right :=
          hP.hom_ext _ _
        have hCompat : p.1.right ≫
              ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl) =
            hP.from (((wedge P).obj X).obj Y).right ≫ p'.2.1.inr := by
          rw [← Category.assoc, hProd, Category.assoc, p'.2.1.condition]
          rw [← Category.assoc, hPoint]
        let t : PushoutCocone p.1.right
            (hP.from (((wedge P).obj X).obj Y).right) :=
          PushoutCocone.mk
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr hCompat
        exact Under.homMk
          (PushoutCocone.IsColimit.desc p.2.2 t.inl t.inr t.condition) (by
          exact PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
      let collapse (A B : Under P) :=
        hP.from (((wedge P).obj A).obj B).right
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      have mq {A A' B B' : Under P}
          (f : A ⟶ A') (g : B ⟶ B') :
          q A B ≫ (smashMap P hP f g).right =
            (f.right ⊗ₘ g.right) ≫ q A' B' := by
        dsimp only [q, smashMap]
        let p := smashPresentation P hP A B
        let p' := smashPresentation P hP A' B'
        change p.2.1.inl ≫ PushoutCocone.IsColimit.desc p.2.2
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr _ =
          (f.right ⊗ₘ g.right) ≫ p'.2.1.inl
        exact PushoutCocone.IsColimit.inl_desc p.2.2 _ _ _
      have smashMap_first {A A' : Under P} (f : A ⟶ A') (B : Under P) :
          smashMap P hP f (𝟙 B) = ((smash P hP).map f).app B := by
        rfl
      let S0 : Under P := Under.mk (coprod.inl : P ⟶ P ⨿ P)
      let eS0 : smashUnit P ≅ S0 := Under.isoMk (Iso.refl _) (by
        dsimp [S0, smashUnit]; simp [Under.costar_obj_hom])
      have eS0_right : eS0.hom.right = 𝟙 _ := rfl
      have sphereZero_hom : (smashUnit P).hom =
          (show P ⟶ (smashUnit P).right from coprod.inl) := by
        dsimp [smashUnit]; simp [Under.costar_obj_hom]
      let p : P ≅ 𝟙_ C :=
        hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
      let prodTo (T : Under P) : S0.right ⊗ T.right ⟶ T.right :=
        (rightDistrib T.right P P).inv ≫
          coprod.desc (hP.from (P ⊗ T.right) ≫ T.hom)
            ((p.hom ▷ T.right) ≫ (λ_ T.right).hom)
      have lu0 (T : Under P) :
          ((smashUnit P).hom ▷ T.right) ≫ q (smashUnit P) T ≫
              (smashLeftUnitor P hP T).hom.right =
            hP.from
              (P ⊗ T.right) ≫ T.hom := by
        dsimp only [smashLeftUnitor]
        simp only [Iso.trans_hom, Under.comp_right]
        have hmf := smashMap_first eS0.hom T
        change ((smashUnit P).hom ▷ T.right) ≫ q (smashUnit P) T ≫
            (((smash P hP).map eS0.hom).app T).right ≫ _ = _
        rw [← hmf]
        slice_lhs 2 3 => rw [mq]
        rw [eS0_right]
        simp only [Under.id_right, MonoidalCategory.id_tensorHom_id, Category.id_comp]
        rw [sphereZero_hom]
        dsimp only [S0, q]
        simp only [pointedPushoutIsoOfDescentData_hom_right]
        calc
          _ = (coprod.inl ▷ T.right) ≫ prodTo T := by
            simpa only [Category.assoc] using congrArg
              (fun k => (coprod.inl ▷ T.right) ≫ k)
              (PushoutCocone.IsColimit.inl_desc
                (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
          _ = _ := by
            dsimp only [prodTo]
            rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
              CategoryTheory.Limits.coprod.inl_desc]
      have lu1 (T : Under P) :
          ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              q (smashUnit P) T ≫ (smashLeftUnitor P hP T).hom.right =
            (p.hom ▷ T.right) ≫ (λ_ T.right).hom := by
        dsimp only [smashLeftUnitor]
        simp only [Iso.trans_hom, Under.comp_right]
        have hmf := smashMap_first eS0.hom T
        change ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            q (smashUnit P) T ≫
            (((smash P hP).map eS0.hom).app T).right ≫ _ = _
        rw [← hmf]
        slice_lhs 2 3 => rw [mq]
        rw [eS0_right]
        simp only [Under.id_right, MonoidalCategory.id_tensorHom_id, Category.id_comp]
        dsimp only [S0, q]
        simp only [pointedPushoutIsoOfDescentData_hom_right]
        calc
          _ = (coprod.inr ▷ T.right) ≫ prodTo T := by
            simpa only [Category.assoc] using congrArg
              (fun k => (coprod.inr ▷ T.right) ≫ k)
              (PushoutCocone.IsColimit.inl_desc
                (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
          _ = _ := by
            dsimp only [prodTo]
            rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
              CategoryTheory.Limits.coprod.inr_desc]
      have lu0Direct (T : Under P) :
          ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              q (smashUnit P) T ≫ (smashLeftUnitor P hP T).hom.right =
            hP.from (P ⊗ T.right) ≫ T.hom := by
        simpa only [sphereZero_hom] using lu0 T
      exact ⟨lu0Direct, lu1⟩
  -- The right unitor retains the quotient formulas.
  smashRightUnitorFormulas
      (smashBraidingData :
        ∀ (P : C) (hP : IsTerminal P) (X Y : Under P),
          { e : ((smash P hP).obj X).obj Y ≅ ((smash P hP).obj Y).obj X //
            (smashPresentation P hP X Y).2.1.inl ≫ e.hom.right =
              CartesianMonoidalCategory.lift
                  (CartesianMonoidalCategory.snd X.right Y.right)
                  (CartesianMonoidalCategory.fst X.right Y.right) ≫
                (smashPresentation P hP Y X).2.1.inl })
      (smashBraiding_eq :
        ∀ (P : C) (hP : IsTerminal P) (A B : Under P),
          smashBraiding P hP A B = (smashBraidingData P hP A B).1)
      (lu0_all :
        ∀ (P : C) (hP : IsTerminal P) (T : Under P),
          ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
              (smashLeftUnitor P hP T).hom.right =
            hP.from (P ⊗ T.right) ≫ T.hom)
      (lu1_all :
        ∀ (P : C) (hP : IsTerminal P) (T : Under P),
          ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
              (smashLeftUnitor P hP T).hom.right =
            ((hP.uniqueUpToIso
                CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ T.right) ≫
              (λ_ T.right).hom)
      (P : C) (hP : IsTerminal P) :
      (∀ T : Under P,
        (T.right ◁ (coprod.inl : P ⟶ (smashUnit P).right)) ≫
            (smashPresentation P hP T (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP T).hom.right =
          hP.from (T.right ⊗ P) ≫ T.hom) ∧
      (∀ T : Under P,
        (T.right ◁ (coprod.inr : P ⟶ (smashUnit P).right)) ≫
            (smashPresentation P hP T (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP T).hom.right =
          (T.right ◁ (hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom) ≫
            (ρ_ T.right).hom) := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      have cq (A B : Under P) :
          q A B ≫ (smashBraidingData P hP A B).1.hom.right =
            (β_ A.right B.right).hom ≫ q B A := by
        simpa only [q, CartesianMonoidalCategory.lift_snd_fst] using
          (smashBraidingData P hP A B).2
      let p : P ≅ 𝟙_ C :=
        hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
      let lu0Direct := lu0_all P hP
      have sphereZero_hom : (smashUnit P).hom =
          (show P ⟶ (smashUnit P).right from coprod.inl) := by
        dsimp [smashUnit]
        simp [Under.costar_obj_hom]
      have lu0 (T : Under P) :
          ((smashUnit P).hom ▷ T.right) ≫ q (smashUnit P) T ≫
              (smashLeftUnitor P hP T).hom.right =
            hP.from (P ⊗ T.right) ≫ T.hom := by
        simpa only [sphereZero_hom] using lu0Direct T
      let lu1 := lu1_all P hP
      have ru0 (T : Under P) :
          (T.right ◁ (smashUnit P).hom) ≫ q T (smashUnit P) ≫
              (smashRightUnitor P hP T).hom.right =
            hP.from
              (T.right ⊗ P) ≫ T.hom := by
        dsimp only [smashRightUnitor, Iso.trans_hom, Under.comp_right]
        rw [smashBraiding_eq P hP]
        slice_lhs 2 3 => rw [cq]
        slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_right]
        simp only [Category.assoc]
        rw [lu0]
        have hp : (β_ T.right P).hom ≫
              hP.from
                (P ⊗ T.right) =
            hP.from
              (T.right ⊗ P) :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using congrArg
          (fun k : T.right ⊗ P ⟶
            P => k ≫ T.hom) hp
      have ru1 (T : Under P) :
          (T.right ◁ (show P ⟶ (smashUnit P).right from
            coprod.inr)) ≫ q T (smashUnit P) ≫
              (smashRightUnitor P hP T).hom.right =
            (T.right ◁ p.hom) ≫ (ρ_ T.right).hom := by
        dsimp only [smashRightUnitor, Iso.trans_hom, Under.comp_right]
        rw [smashBraiding_eq P hP]
        slice_lhs 2 3 => rw [cq]
        slice_lhs 1 2 => rw [BraidedCategory.braiding_naturality_right]
        simp only [Category.assoc]
        rw [lu1]
        slice_lhs 1 2 => rw [← BraidedCategory.braiding_naturality_right]
        rw [braiding_tensorUnit_right]
        slice_lhs 3 4 => rw [Iso.inv_hom_id]
        rw [Category.comp_id]
      have ru0Direct (T : Under P) :
          (T.right ◁ (coprod.inl : P ⟶ (smashUnit P).right)) ≫
              q T (smashUnit P) ≫ (smashRightUnitor P hP T).hom.right =
            hP.from (T.right ⊗ P) ≫ T.hom := by
        simpa only [sphereZero_hom] using ru0 T
      exact ⟨ru0Direct, ru1⟩
  -- The same unitors satisfy triangle coherence.
  smashTriangleCore (P : C) (hP : IsTerminal P)
      (X Y : Under P)
      (lu0 :
        ((coprod.inl : P ⟶ (smashUnit P).right) ▷ Y.right) ≫
            (smashPresentation P hP (smashUnit P) Y).2.1.inl ≫
            (smashLeftUnitor P hP Y).hom.right =
          hP.from (P ⊗ Y.right) ≫ Y.hom)
      (lu1 :
        ((coprod.inr : P ⟶ (smashUnit P).right) ▷ Y.right) ≫
            (smashPresentation P hP (smashUnit P) Y).2.1.inl ≫
            (smashLeftUnitor P hP Y).hom.right =
          ((hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ Y.right) ≫
            (λ_ Y.right).hom)
      (ru0 :
        (X.right ◁ (coprod.inl : P ⟶ (smashUnit P).right)) ≫
            (smashPresentation P hP X (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP X).hom.right =
          hP.from (X.right ⊗ P) ≫ X.hom)
      (ru1 :
        (X.right ◁ (coprod.inr : P ⟶ (smashUnit P).right)) ≫
            (smashPresentation P hP X (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP X).hom.right =
          (X.right ◁ (hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom) ≫
            (ρ_ X.right).hom)
      (hQLeftMap : ∀ (A B : Under P) {T : C} (f : T ⟶ A.right),
        CartesianMonoidalCategory.lift f (hP.from T ≫ B.hom) ≫
            (smashPresentation P hP A B).2.1.inl =
          hP.from T ≫ (smashPresentation P hP A B).2.1.inr)
      (hQRightMap : ∀ (A B : Under P) {T : C} (f : T ⟶ B.right),
        CartesianMonoidalCategory.lift (hP.from T ≫ A.hom) f ≫
            (smashPresentation P hP A B).2.1.inl =
          hP.from T ≫ (smashPresentation P hP A B).2.1.inr) :
      (α_ X.right (smashUnit P).right Y.right).hom ≫
          X.right ◁
            ((smashPresentation P hP (smashUnit P) Y).2.1.inl ≫
              (smashLeftUnitor P hP Y).hom.right) ≫
          (smashPresentation P hP X Y).2.1.inl =
        ((smashPresentation P hP X (smashUnit P)).2.1.inl ≫
            (smashRightUnitor P hP X).hom.right) ▷ Y.right ≫
          (smashPresentation P hP X Y).2.1.inl := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      let p : P ≅ 𝟙_ C :=
        hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
      let cover := (rightDistrib Y.right
          (X.right ⊗ P) (X.right ⊗ P)).hom ≫
        ((leftDistrib X.right P P).hom ▷ Y.right)
      let D := (X.right ⊗ P) ⊗ Y.right
      let E := X.right ⊗ P
      let coverBase : D ⟶ D ⨿ D := coprod.inl
      let coverFree : D ⟶ D ⨿ D := coprod.inr
      let innerBase : E ⟶ E ⨿ E := coprod.inl
      let innerFree : E ⟶ E ⨿ E := coprod.inr
      let s0Base : P ⟶ (smashUnit P).right :=
        (show P ⟶ (smashUnit P).right from coprod.inl)
      let s0Free : P ⟶ (smashUnit P).right :=
        (show P ⟶ (smashUnit P).right from coprod.inr)
      have hCoverBase : coverBase ≫ cover =
          (X.right ◁ s0Base) ▷ Y.right := by
        calc
          coverBase ≫ cover =
              (innerBase ▷ Y.right) ≫
                ((leftDistrib X.right P P).hom ▷ Y.right) := by
            dsimp only [cover, coverBase, innerBase, D, E]
            simpa only [Category.assoc] using congrArg
              (fun k => k ≫ ((leftDistrib X.right P P).hom ▷ Y.right))
              (coprod_inl_rightDistrib_hom (C := C)
                (X := Y.right) (Y := X.right ⊗ P) (Z := X.right ⊗ P))
          _ = (X.right ◁ s0Base) ▷ Y.right := by
            simpa only [MonoidalCategory.comp_whiskerRight] using congrArg
              (fun k => k ▷ Y.right)
              (coprod_inl_leftDistrib_hom (C := C)
                (X := X.right) (Y := P) (Z := P))
      have hCoverFree : coverFree ≫ cover =
          (X.right ◁ s0Free) ▷ Y.right := by
        calc
          coverFree ≫ cover =
              (innerFree ▷ Y.right) ≫
                ((leftDistrib X.right P P).hom ▷ Y.right) := by
            dsimp only [cover, coverFree, innerFree, D, E]
            simpa only [Category.assoc] using congrArg
              (fun k => k ≫ ((leftDistrib X.right P P).hom ▷ Y.right))
              (coprod_inr_rightDistrib_hom (C := C)
                (X := Y.right) (Y := X.right ⊗ P) (Z := X.right ⊗ P))
          _ = (X.right ◁ s0Free) ▷ Y.right := by
            simpa only [MonoidalCategory.comp_whiskerRight] using congrArg
              (fun k => k ▷ Y.right)
              (coprod_inr_leftDistrib_hom (C := C)
                (X := X.right) (Y := P) (Z := P))
      dsimp only [coverBase, coverFree, D] at hCoverBase hCoverFree
      let _ : Epi cover := inferInstance
      apply (cancel_epi cover).1
      apply coprod.hom_ext
      · rw [← Category.assoc, hCoverBase]
        conv_rhs => rw [← Category.assoc, hCoverBase]
        dsimp only [s0Base]
        slice_lhs 1 2 =>
          rw [MonoidalCategory.associator_naturality_middle X.right
            s0Base Y.right]
        slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp]
        rw [lu0]
        slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight]
        rw [ru0]
        let T0 := (X.right ⊗ P) ⊗ Y.right
        let fX : T0 ⟶ X.right :=
          (α_ X.right P Y.right).hom ≫
            CartesianMonoidalCategory.fst X.right
              (P ⊗ Y.right)
        let fY : T0 ⟶ Y.right :=
          CartesianMonoidalCategory.snd
            (X.right ⊗ P) Y.right
        have hLeftPre :
            (α_ X.right P Y.right).hom ≫
                (X.right ◁ (hP.from
                  (P ⊗ Y.right) ≫ Y.hom)) =
              CartesianMonoidalCategory.lift fX
                (hP.from T0 ≫ Y.hom) := by
          apply CartesianMonoidalCategory.hom_ext
          · simp [fX]
          · simp only [Category.assoc,
              CartesianMonoidalCategory.lift_snd]
            rw [CartesianMonoidalCategory.whiskerLeft_snd]
            have hp : (α_ X.right P Y.right).hom ≫
                  CartesianMonoidalCategory.snd X.right
                    (P ⊗ Y.right) ≫
                  hP.from
                    (P ⊗ Y.right) =
                hP.from T0 :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using congrArg
              (fun k : T0 ⟶ P => k ≫ Y.hom) hp
        have hRightPre :
            (hP.from
                  (X.right ⊗ P) ≫ X.hom) ▷ Y.right =
              CartesianMonoidalCategory.lift
                (hP.from T0 ≫ X.hom) fY := by
          apply CartesianMonoidalCategory.hom_ext
          · simp only [CartesianMonoidalCategory.lift_fst]
            rw [CartesianMonoidalCategory.whiskerRight_fst]
            have hp : CartesianMonoidalCategory.fst
                  (X.right ⊗ P) Y.right ≫
                  hP.from
                    (X.right ⊗ P) =
                hP.from T0 :=
              hP.hom_ext _ _
            simpa only [Category.assoc] using congrArg
              (fun k : T0 ⟶ P => k ≫ X.hom) hp
          · simp [fY]
        rw [← Category.assoc, hLeftPre]
        rw [hRightPre, hQLeftMap, hQRightMap]
      · rw [← Category.assoc, hCoverFree]
        conv_rhs => rw [← Category.assoc, hCoverFree]
        dsimp only [s0Free]
        slice_lhs 1 2 =>
          rw [MonoidalCategory.associator_naturality_middle X.right
            s0Free Y.right]
        slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp]
        rw [lu1]
        slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight]
        rw [ru1]
        rw [MonoidalCategory.whiskerLeft_comp]
        slice_lhs 1 2 =>
          rw [← MonoidalCategory.associator_naturality_middle X.right p.hom Y.right]
        slice_lhs 2 3 => rw [MonoidalCategory.triangle]
        rw [MonoidalCategory.comp_whiskerRight]
        simp only [Category.assoc]
        rfl


private theorem smashMonoidalAssociatorNaturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Under P}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    μ (μ f₁ f₂) f₃ ≫ (smashAssociator P hP Y₁ Y₂ Y₃).hom =
      (smashAssociator P hP X₁ X₂ X₃).hom ≫ μ f₁ (μ f₂ f₃) := by
  dsimp only
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, epiQR, _epiQRR, _tensorDef, _identity, _composition⟩
  exact smashAssociatorNaturality P hP
    (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
    map_q (smashAssociator P hP) (smashAssociator_hom_quotient P hP)
    epiQ epiQR f₁ f₂ f₃
where
  smashAssociatorNaturality (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (map_q : ∀ {A A' B B' : Under P}
        (f : A ⟶ A') (g : B ⟶ B'),
        (smashPresentation P hP A B).2.1.inl ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫
            (smashPresentation P hP A' B').2.1.inl)
      (smashAssociator : ∀ A B D : Under P,
        ((smash P hP).obj (((smash P hP).obj A).obj B)).obj D ≅
          ((smash P hP).obj A).obj (((smash P hP).obj B).obj D))
      (assoc_q : ∀ A B D : Under P,
        (((smashPresentation P hP A B).2.1.inl ▷ D.right) ≫
            (smashPresentation P hP (((smash P hP).obj A).obj B) D).2.1.inl) ≫
            (smashAssociator A B D).hom.right =
          (α_ A.right B.right D.right).hom ≫
            (A.right ◁ (smashPresentation P hP B D).2.1.inl) ≫
            (smashPresentation P hP A (((smash P hP).obj B).obj D)).2.1.inl)
      (epiQ : ∀ A B : Under P,
        Epi (smashPresentation P hP A B).2.1.inl)
      (epiQR : ∀ (A B : Under P) (T : C),
        Epi ((smashPresentation P hP A B).2.1.inl ▷ T))
      {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Under P}
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
      smashMap (smashMap f₁ f₂) f₃ ≫ (smashAssociator Y₁ Y₂ Y₃).hom =
        (smashAssociator X₁ X₂ X₃).hom ≫
          smashMap f₁ (smashMap f₂ f₃) := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      change smashMap (smashMap f₁ f₂) f₃ ≫
          (smashAssociator Y₁ Y₂ Y₃).hom =
        (smashAssociator X₁ X₂ X₃).hom ≫
          smashMap f₁ (smashMap f₂ f₃)
      let S12 := ((smash P hP).obj X₁).obj X₂
      let _ : Epi (q S12 X₃) := epiQ S12 X₃
      let _ : Epi (q X₁ X₂ ▷ X₃.right) := epiQR X₁ X₂ X₃.right
      apply Under.UnderMorphism.ext
      apply (cancel_epi (q S12 X₃)).1
      apply (cancel_epi (q X₁ X₂ ▷ X₃.right)).1
      simp only [Under.comp_right]
      slice_lhs 2 3 => rw [map_q]
      slice_lhs 1 2 =>
        rw [MonoidalCategory.whiskerRight_comp_tensorHom]
      rw [map_q f₁ f₂]
      have ht : ((f₁.right ⊗ₘ f₂.right) ≫ q Y₁ Y₂) ⊗ₘ f₃.right =
          ((f₁.right ⊗ₘ f₂.right) ⊗ₘ f₃.right) ≫
            (q Y₁ Y₂ ▷ Y₃.right) := by
        simpa only [Category.comp_id, MonoidalCategory.tensorHom_id] using
          (MonoidalCategory.tensorHom_comp_tensorHom
            (f₁.right ⊗ₘ f₂.right) f₃.right (q Y₁ Y₂) (𝟙 Y₃.right)).symm
      rw [ht]
      simp only [Category.assoc]
      slice_lhs 2 4 => rw [← Category.assoc, assoc_q]
      slice_rhs 1 3 => rw [← Category.assoc, assoc_q]
      slice_rhs 3 4 => rw [map_q]
      slice_rhs 2 3 =>
        rw [MonoidalCategory.whiskerLeft_comp_tensorHom]
      rw [map_q f₂ f₃]
      have ht' : f₁.right ⊗ₘ
            ((f₂.right ⊗ₘ f₃.right) ≫ q Y₂ Y₃) =
          (f₁.right ⊗ₘ (f₂.right ⊗ₘ f₃.right)) ≫
            (Y₁.right ◁ q Y₂ Y₃) := by
        simpa only [Category.comp_id, MonoidalCategory.id_tensorHom] using
          (MonoidalCategory.tensorHom_comp_tensorHom f₁.right
            (f₂.right ⊗ₘ f₃.right) (𝟙 Y₁.right) (q Y₂ Y₃)).symm
      rw [ht']
      let tail := (Y₁.right ◁ q Y₂ Y₃) ≫ q Y₁ (((smash P hP).obj Y₂).obj Y₃)
      simpa only [Category.assoc, tail] using congrArg (fun k => k ≫ tail)
        (MonoidalCategory.associator_naturality f₁.right f₂.right f₃.right)


private theorem smashMonoidalLeftUnitorNaturality
    {X Y : Under P} (f : X ⟶ Y) :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    μ (𝟙 (smashUnit P)) f ≫ (smashLeftUnitor P hP Y).hom =
      (smashLeftUnitor P hP X).hom ≫ f := by
  dsimp only
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, _epiQR, _epiQRR, _tensorDef, _identity, _composition⟩
  have leftData := smashLeftUnitorFormulas P hP
  exact smashLeftNaturality P hP
    (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
    map_q epiQ leftData.1 leftData.2 f
where
  smashLeftUnitorFormulas (P : C)
      (hP : IsTerminal P) :
      (∀ T : Under P,
        ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          hP.from (P ⊗ T.right) ≫ T.hom) ∧
      (∀ T : Under P,
        ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          ((hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ T.right) ≫
            (λ_ T.right).hom) := by
    set_option backward.isDefEq.respectTransparency false in
      let smashPushout (P : C) (hP : IsTerminal P)
          (X Y : Under P) : Under P :=
        Under.mk
          (show P ⟶ (smashPresentation P hP X Y).2.1.pt from
            (smashPresentation P hP X Y).2.1.inr)
      let smashMap (P : C) (hP : IsTerminal P)
          {X X' Y Y' : Under P}
          (f : X ⟶ X') (g : Y ⟶ Y') :
          smashPushout P hP X Y ⟶ smashPushout P hP X' Y' := by
        let p := smashPresentation P hP X Y
        let p' := smashPresentation P hP X' Y'
        let wedgeMap : ((wedge P).obj X).obj Y ⟶
            ((wedge P).obj X').obj Y' :=
          Under.homMk
            (pushout.map X.hom Y.hom X'.hom Y'.hom f.right g.right
              (𝟙 P)
              (by simpa only [Category.id_comp] using Under.w f)
              (by simpa only [Category.id_comp] using Under.w g)) (by
                dsimp [wedge]
                rw [Category.assoc, pushout.inl_desc,
                  ← Category.assoc, Under.w f])
        have hProd : p.1.right ≫ (f.right ⊗ₘ g.right) =
            wedgeMap.right ≫ p'.1.right := by
          dsimp only [p, p', smashPresentation]
          dsimp only [wedgeMap, Under.homMk_right]
          apply pushout.hom_ext
          · apply CartesianMonoidalCategory.hom_ext
            · simp [Category.assoc]
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_left, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.id_comp, Category.assoc,
                Under.w, CartesianMonoidalCategory.lift_snd, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from X.right)
                  (f.right ≫ hP.from X'.right)]
          · apply CartesianMonoidalCategory.hom_ext
            · simp only [Under.mk_right, Under.homMk_right, colimit.ι_desc_assoc,
                span_right, PushoutCocone.mk_pt, PushoutCocone.mk_ι_app,
                CartesianMonoidalCategory.lift_map, Category.assoc, Under.w,
                Category.id_comp, CartesianMonoidalCategory.lift_fst, colimit.ι_desc,
                CartesianMonoidalCategory.comp_lift, Category.comp_id]
              rw [← Category.assoc,
                hP.hom_ext (hP.from Y.right)
                  (g.right ≫ hP.from Y'.right)]
            · simp [Category.assoc]
        have hPoint : wedgeMap.right ≫
            hP.from (((wedge P).obj X').obj Y').right =
          hP.from (((wedge P).obj X).obj Y).right :=
          hP.hom_ext _ _
        have hCompat : p.1.right ≫
              ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl) =
            hP.from (((wedge P).obj X).obj Y).right ≫ p'.2.1.inr := by
          rw [← Category.assoc, hProd, Category.assoc, p'.2.1.condition]
          rw [← Category.assoc, hPoint]
        let t : PushoutCocone p.1.right
            (hP.from (((wedge P).obj X).obj Y).right) :=
          PushoutCocone.mk
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr hCompat
        exact Under.homMk
          (PushoutCocone.IsColimit.desc p.2.2 t.inl t.inr t.condition) (by
          exact PushoutCocone.IsColimit.inr_desc p.2.2 _ _ _)
      let collapse (A B : Under P) :=
        hP.from (((wedge P).obj A).obj B).right
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      have mq {A A' B B' : Under P}
          (f : A ⟶ A') (g : B ⟶ B') :
          q A B ≫ (smashMap P hP f g).right =
            (f.right ⊗ₘ g.right) ≫ q A' B' := by
        dsimp only [q, smashMap]
        let p := smashPresentation P hP A B
        let p' := smashPresentation P hP A' B'
        change p.2.1.inl ≫ PushoutCocone.IsColimit.desc p.2.2
            ((f.right ⊗ₘ g.right) ≫ p'.2.1.inl)
            p'.2.1.inr _ =
          (f.right ⊗ₘ g.right) ≫ p'.2.1.inl
        exact PushoutCocone.IsColimit.inl_desc p.2.2 _ _ _
      have smashMap_first {A A' : Under P} (f : A ⟶ A') (B : Under P) :
          smashMap P hP f (𝟙 B) = ((smash P hP).map f).app B := by
        rfl
      let S0 : Under P := Under.mk (coprod.inl : P ⟶ P ⨿ P)
      let eS0 : smashUnit P ≅ S0 := Under.isoMk (Iso.refl _) (by
        dsimp [S0, smashUnit]; simp [Under.costar_obj_hom])
      have eS0_right : eS0.hom.right = 𝟙 _ := rfl
      have sphereZero_hom : (smashUnit P).hom =
          (show P ⟶ (smashUnit P).right from coprod.inl) := by
        dsimp [smashUnit]; simp [Under.costar_obj_hom]
      let p : P ≅ 𝟙_ C :=
        hP.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
      let prodTo (T : Under P) : S0.right ⊗ T.right ⟶ T.right :=
        (rightDistrib T.right P P).inv ≫
          coprod.desc (hP.from (P ⊗ T.right) ≫ T.hom)
            ((p.hom ▷ T.right) ≫ (λ_ T.right).hom)
      have lu0 (T : Under P) :
          ((smashUnit P).hom ▷ T.right) ≫ q (smashUnit P) T ≫
              (smashLeftUnitor P hP T).hom.right =
            hP.from
              (P ⊗ T.right) ≫ T.hom := by
        dsimp only [smashLeftUnitor]
        simp only [Iso.trans_hom, Under.comp_right]
        have hmf := smashMap_first eS0.hom T
        change ((smashUnit P).hom ▷ T.right) ≫ q (smashUnit P) T ≫
            (((smash P hP).map eS0.hom).app T).right ≫ _ = _
        rw [← hmf]
        slice_lhs 2 3 => rw [mq]
        rw [eS0_right]
        simp only [Under.id_right, MonoidalCategory.id_tensorHom_id, Category.id_comp]
        rw [sphereZero_hom]
        dsimp only [S0, q]
        simp only [pointedPushoutIsoOfDescentData_hom_right]
        calc
          _ = (coprod.inl ▷ T.right) ≫ prodTo T := by
            simpa only [Category.assoc] using congrArg
              (fun k => (coprod.inl ▷ T.right) ≫ k)
              (PushoutCocone.IsColimit.inl_desc
                (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
          _ = _ := by
            dsimp only [prodTo]
            rw [CategoryTheory.whiskerRight_coprod_inl_rightDistrib_inv_assoc,
              CategoryTheory.Limits.coprod.inl_desc]
      have lu1 (T : Under P) :
          ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              q (smashUnit P) T ≫ (smashLeftUnitor P hP T).hom.right =
            (p.hom ▷ T.right) ≫ (λ_ T.right).hom := by
        dsimp only [smashLeftUnitor]
        simp only [Iso.trans_hom, Under.comp_right]
        have hmf := smashMap_first eS0.hom T
        change ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            q (smashUnit P) T ≫
            (((smash P hP).map eS0.hom).app T).right ≫ _ = _
        rw [← hmf]
        slice_lhs 2 3 => rw [mq]
        rw [eS0_right]
        simp only [Under.id_right, MonoidalCategory.id_tensorHom_id, Category.id_comp]
        dsimp only [S0, q]
        simp only [pointedPushoutIsoOfDescentData_hom_right]
        calc
          _ = (coprod.inr ▷ T.right) ≫ prodTo T := by
            simpa only [Category.assoc] using congrArg
              (fun k => (coprod.inr ▷ T.right) ≫ k)
              (PushoutCocone.IsColimit.inl_desc
                (smashPresentation P hP (Under.mk coprod.inl) T).2.2 _ _ _)
          _ = _ := by
            dsimp only [prodTo]
            rw [CategoryTheory.whiskerRight_coprod_inr_rightDistrib_inv_assoc,
              CategoryTheory.Limits.coprod.inr_desc]
      have lu0Direct (T : Under P) :
          ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
              q (smashUnit P) T ≫ (smashLeftUnitor P hP T).hom.right =
            hP.from (P ⊗ T.right) ≫ T.hom := by
        simpa only [sphereZero_hom] using lu0 T
      exact ⟨lu0Direct, lu1⟩
  -- The left unitor is natural in the same pointed maps.
  smashLeftNaturality (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (map_q : ∀ {A A' B B' : Under P}
        (f : A ⟶ A') (g : B ⟶ B'),
        (smashPresentation P hP A B).2.1.inl ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫
            (smashPresentation P hP A' B').2.1.inl)
      (epiQ : ∀ A B : Under P,
        Epi (smashPresentation P hP A B).2.1.inl)
      (lu0 : ∀ T : Under P,
        ((coprod.inl : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          hP.from (P ⊗ T.right) ≫ T.hom)
      (lu1 : ∀ T : Under P,
        ((coprod.inr : P ⟶ (smashUnit P).right) ▷ T.right) ≫
            (smashPresentation P hP (smashUnit P) T).2.1.inl ≫
            (smashLeftUnitor P hP T).hom.right =
          ((hP.uniqueUpToIso
              CartesianMonoidalCategory.isTerminalTensorUnit).hom ▷ T.right) ≫
            (λ_ T.right).hom)
      {X Y : Under P} (f : X ⟶ Y) :
      smashMap (𝟙 (smashUnit P)) f ≫ (smashLeftUnitor P hP Y).hom =
        (smashLeftUnitor P hP X).hom ≫ f := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      let lHom (T : Under P) := (smashLeftUnitor P hP T).hom
      let _ : Epi (q (smashUnit P) X) := epiQ (smashUnit P) X
      apply Under.UnderMorphism.ext
      apply (cancel_epi (q (smashUnit P) X)).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      let cover := (rightDistrib X.right P P).hom
      have h0 : coprod.inl ≫ cover = coprod.inl ▷ X.right := by
        exact coprod_inl_rightDistrib_hom
      have h1 : coprod.inr ≫ cover = coprod.inr ▷ X.right := by
        exact coprod_inr_rightDistrib_hom
      let _ : Epi cover := inferInstance
      apply (cancel_epi cover).1
      apply coprod.hom_ext
      · simp only [← Category.assoc, h0]
        slice_lhs 1 2 =>
          change (coprod.inl ▷ X.right) ≫ ((P ⨿ P) ◁ f.right)
          rw [← MonoidalCategory.whisker_exchange coprod.inl f.right]
        simp only [Category.assoc]
        slice_lhs 2 4 => rw [lu0]
        slice_rhs 1 3 => rw [lu0]
        rw [Category.assoc, Under.w f]
        have hp : (P ◁ f.right) ≫
              hP.from
                (P ⊗ Y.right) =
            hP.from
              (P ⊗ X.right) :=
          hP.hom_ext _ _
        simpa only [Category.assoc] using congrArg (fun k => k ≫ Y.hom) hp
      · simp only [← Category.assoc, h1]
        slice_lhs 1 2 =>
          change (coprod.inr ▷ X.right) ≫ ((P ⨿ P) ◁ f.right)
          rw [← MonoidalCategory.whisker_exchange coprod.inr f.right]
        simp only [Category.assoc]
        slice_lhs 2 4 => rw [lu1]
        slice_rhs 1 3 => rw [lu1]
        slice_lhs 1 2 => rw [MonoidalCategory.whisker_exchange]
        slice_lhs 2 3 => rw [MonoidalCategory.leftUnitor_naturality]
        simp only [Category.assoc]

private theorem smashMonoidalRightUnitorNaturality
    {X Y : Under P} (f : X ⟶ Y) :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    μ f (𝟙 (smashUnit P)) ≫ (smashRightUnitor P hP Y).hom =
      (smashRightUnitor P hP X).hom ≫ f := by
  dsimp only
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, _epiQR, _epiQRR, _tensorDef, _identity, _composition⟩
  have braid_q := (smashMonoidalUnitCore P hP).1
  have braidNat {X Y : Under P} (f : X ⟶ Y) :=
    smashBraidingNaturality P hP
      (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
      map_q (smashBraiding P hP) braid_q epiQ f
  exact smashRightUnitorNaturality P hP
    (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
    braidNat (smashMonoidalLeftUnitorNaturality P hP) f
where
  smashBraidingNaturality
      (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (map_q : ∀ {A A' B B' : Under P}
        (f : A ⟶ A') (g : B ⟶ B'),
        (smashPresentation P hP A B).2.1.inl ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫
            (smashPresentation P hP A' B').2.1.inl)
      (smashBraiding : ∀ A B : Under P,
        ((smash P hP).obj A).obj B ≅ ((smash P hP).obj B).obj A)
      (braid_q : ∀ A B : Under P,
        (smashPresentation P hP A B).2.1.inl ≫
            (smashBraiding A B).hom.right =
          (β_ A.right B.right).hom ≫
            (smashPresentation P hP B A).2.1.inl)
      (epiQ : ∀ A B : Under P,
        Epi (smashPresentation P hP A B).2.1.inl)
      {X Y : Under P} (f : X ⟶ Y) :
      smashMap f (𝟙 (smashUnit P)) ≫
          (smashBraiding Y (smashUnit P)).hom =
        (smashBraiding X (smashUnit P)).hom ≫
          smashMap (𝟙 (smashUnit P)) f := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      apply Under.UnderMorphism.ext
      let _ : Epi (q X (smashUnit P)) := epiQ X (smashUnit P)
      apply (cancel_epi (q X (smashUnit P))).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id]
      slice_lhs 2 3 => rw [braid_q]
      slice_rhs 1 2 => rw [braid_q]
      slice_rhs 2 3 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ q (smashUnit P) Y)
          (BraidedCategory.braiding_naturality_left
            f.right (smashUnit P).right)
  -- The right unitor is natural in the same pointed maps.
  smashRightUnitorNaturality
      (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (braidNat : ∀ {X Y : Under P} (f : X ⟶ Y),
        smashMap f (𝟙 (smashUnit P)) ≫
            (smashBraiding P hP Y (smashUnit P)).hom =
          (smashBraiding P hP X (smashUnit P)).hom ≫
            smashMap (𝟙 (smashUnit P)) f)
      (leftNat : ∀ {X Y : Under P} (f : X ⟶ Y),
        smashMap (𝟙 (smashUnit P)) f ≫
            (smashLeftUnitor P hP Y).hom =
          (smashLeftUnitor P hP X).hom ≫ f)
      {X Y : Under P} (f : X ⟶ Y) :
      smashMap f (𝟙 (smashUnit P)) ≫
          (smashRightUnitor P hP Y).hom =
        (smashRightUnitor P hP X).hom ≫ f := by
    set_option backward.isDefEq.respectTransparency false in
      dsimp only [smashRightUnitor, Iso.trans_hom]
      rw [← Category.assoc, braidNat f, Category.assoc, leftNat f]
      simp only [Category.assoc]


private theorem smashMonoidalPentagon (W X Y Z : Under P) :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    μ (smashAssociator P hP W X Y).hom (𝟙 Z) ≫
          (smashAssociator P hP W (((smash P hP).obj X).obj Y) Z).hom ≫
        μ (𝟙 W) (smashAssociator P hP X Y Z).hom =
      (smashAssociator P hP (((smash P hP).obj W).obj X) Y Z).hom ≫
        (smashAssociator P hP W X (((smash P hP).obj Y).obj Z)).hom := by
  dsimp only
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, epiQR, epiQRR, _tensorDef, _identity, _composition⟩
  exact smashPentagonAux P hP W X Y Z
    (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
    (fun A B => (smashPresentation P hP A B).2.1.inl) map_q
    (smashAssociator P hP) (smashAssociator_hom_quotient P hP)
    epiQ epiQR (epiQRR W X Y.right Z.right)
where
  smashPentagonAux (P : C) (hP : IsTerminal P)
      (W X Y Z : Under P)
      (smashMap :
        ∀ {A A' B B' : Under P}, (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (q : ∀ A B : Under P,
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right)
      (map_q_all :
        ∀ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B'),
          q A B ≫ (smashMap f g).right =
            (f.right ⊗ₘ g.right) ≫ q A' B')
      (smashAssociator : ∀ A B D : Under P,
        ((smash P hP).obj (((smash P hP).obj A).obj B)).obj D ≅
          ((smash P hP).obj A).obj (((smash P hP).obj B).obj D))
      (assoc_q_all : ∀ A B D : Under P,
        (((q A B ▷ D.right) ≫ q (((smash P hP).obj A).obj B) D) ≫
            (smashAssociator A B D).hom.right =
          (α_ A.right B.right D.right).hom ≫
            (A.right ◁ q B D) ≫
            q A (((smash P hP).obj B).obj D)))
      (epiQ_all : ∀ A B : Under P, Epi (q A B))
      (epiQR_all : ∀ (A B : Under P) (T : C), Epi (q A B ▷ T))
      (epiQRR : Epi ((q W X ▷ Y.right) ▷ Z.right)) :
      smashMap (smashAssociator W X Y).hom (𝟙 Z) ≫
          (smashAssociator W (((smash P hP).obj X).obj Y) Z).hom ≫
          smashMap (𝟙 W) (smashAssociator X Y Z).hom =
        (smashAssociator (((smash P hP).obj W).obj X) Y Z).hom ≫
          (smashAssociator W X (((smash P hP).obj Y).obj Z)).hom := by
    set_option backward.isDefEq.respectTransparency false in
      let assoc_q := assoc_q_all
      have assoc_q_right (A B D : Under P)
          (T : C) :
          (((q A B ▷ D.right) ▷ T) ≫
              (q (((smash P hP).obj A).obj B) D ▷ T)) ≫
              ((smashAssociator A B D).hom.right ▷ T) =
            ((α_ A.right B.right D.right).hom ▷ T) ≫
              ((A.right ◁ q B D) ▷ T) ≫
              (q A (((smash P hP).obj B).obj D) ▷ T) := by
        simpa only [MonoidalCategory.comp_whiskerRight, Category.assoc] using
          congrArg (fun k => k ▷ T) (assoc_q A B D)
      have assoc_q_left (A B D : Under P)
          (T : C) :
          ((T ◁ (q A B ▷ D.right)) ≫
              (T ◁ q (((smash P hP).obj A).obj B) D)) ≫
              (T ◁ (smashAssociator A B D).hom.right) =
            (T ◁ (α_ A.right B.right D.right).hom) ≫
              (T ◁ (A.right ◁ q B D)) ≫
              (T ◁ q A (((smash P hP).obj B).obj D)) := by
        simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
          congrArg (fun k => T ◁ k) (assoc_q A B D)
      let map_q {A A' B B' : Under P}
          (f : A ⟶ A') (g : B ⟶ B') :=
        map_q_all f g
      let epiQ := epiQ_all
      let epiQR := epiQR_all
      let S1 := ((smash P hP).obj W).obj X
      let S2 := ((smash P hP).obj S1).obj Y
      let _ : Epi (q S2 Z) := epiQ S2 Z
      let _ : Epi (q S1 Y ▷ Z.right) := epiQR S1 Y Z.right
      let _ : Epi ((q W X ▷ Y.right) ▷ Z.right) := epiQRR
      apply Under.UnderMorphism.ext
      apply (cancel_epi (q S2 Z)).1
      apply (cancel_epi (q S1 Y ▷ Z.right)).1
      apply (cancel_epi ((q W X ▷ Y.right) ▷ Z.right)).1
      simp only [Under.comp_right]
      slice_lhs 3 4 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id]
      slice_lhs 1 3 => rw [← Category.assoc, assoc_q_right]
      slice_lhs 3 5 => rw [← Category.assoc, assoc_q]
      slice_lhs 2 3 => rw [MonoidalCategory.associator_naturality_middle]
      simp only [Category.assoc]
      slice_lhs 5 6 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      slice_lhs 3 5 => rw [← Category.assoc, assoc_q_left]
      slice_rhs 2 4 => rw [← Category.assoc, assoc_q]
      slice_rhs 1 2 => rw [MonoidalCategory.associator_naturality_left]
      slice_rhs 2 3 => rw [← MonoidalCategory.whisker_exchange]
      slice_rhs 3 5 => rw [← Category.assoc, assoc_q]
      slice_rhs 2 3 => rw [MonoidalCategory.associator_naturality_right]
      let tail := (W.right ◁ (X.right ◁ q Y Z)) ≫
        (W.right ◁ q X (((smash P hP).obj Y).obj Z)) ≫
        q W (((smash P hP).obj X).obj (((smash P hP).obj Y).obj Z))
      simpa only [Category.assoc, tail] using congrArg (fun k => k ≫ tail)
        (MonoidalCategory.pentagon W.right X.right Y.right Z.right)


private theorem smashMonoidalTriangle (X Y : Under P) :
    let μ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
      ((smash P hP).map f).app B ≫ ((smash P hP).obj A').map g
    (smashAssociator P hP X (smashUnit P) Y).hom ≫
        μ (𝟙 X) (smashLeftUnitor P hP Y).hom =
      μ (smashRightUnitor P hP X).hom (𝟙 Y) := by
  dsimp only
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, epiQR, _epiQRR, _tensorDef, _identity, _composition⟩
  exact smashTriangleIdentity P hP
    (fun f g => ((smash P hP).map f).app _ ≫ ((smash P hP).obj _).map g)
    map_q (smashAssociator P hP) (smashAssociator_hom_quotient P hP)
    epiQ epiQR ((smashMonoidalUnitCore P hP).2 X Y)
where
  smashTriangleIdentity
      (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (map_q : ∀ {A A' B B' : Under P}
        (f : A ⟶ A') (g : B ⟶ B'),
        (smashPresentation P hP A B).2.1.inl ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫
            (smashPresentation P hP A' B').2.1.inl)
      (smashAssociator : ∀ A B D : Under P,
        ((smash P hP).obj (((smash P hP).obj A).obj B)).obj D ≅
          ((smash P hP).obj A).obj (((smash P hP).obj B).obj D))
      (assoc_q : ∀ A B D : Under P,
        (((smashPresentation P hP A B).2.1.inl ▷ D.right) ≫
            (smashPresentation P hP
              (((smash P hP).obj A).obj B) D).2.1.inl) ≫
            (smashAssociator A B D).hom.right =
          (α_ A.right B.right D.right).hom ≫
            (A.right ◁ (smashPresentation P hP B D).2.1.inl) ≫
            (smashPresentation P hP A
              (((smash P hP).obj B).obj D)).2.1.inl)
      (epiQ : ∀ A B : Under P,
        Epi (smashPresentation P hP A B).2.1.inl)
      (epiQR : ∀ (A B : Under P) (T : C),
        Epi ((smashPresentation P hP A B).2.1.inl ▷ T))
      {X Y : Under P}
      (core :
        (α_ X.right (smashUnit P).right Y.right).hom ≫
              X.right ◁
                ((smashPresentation P hP (smashUnit P) Y).2.1.inl ≫
                  (smashLeftUnitor P hP Y).hom.right) ≫
            (smashPresentation P hP X Y).2.1.inl =
          ((smashPresentation P hP X (smashUnit P)).2.1.inl ≫
              (smashRightUnitor P hP X).hom.right) ▷ Y.right ≫
            (smashPresentation P hP X Y).2.1.inl) :
      (smashAssociator X (smashUnit P) Y).hom ≫
          smashMap (𝟙 X) (smashLeftUnitor P hP Y).hom =
        smashMap (smashRightUnitor P hP X).hom (𝟙 Y) := by
    set_option backward.isDefEq.respectTransparency false in
      let q (A B : Under P) :
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
        (smashPresentation P hP A B).2.1.inl
      let _ : Epi (q (((smash P hP).obj X).obj (smashUnit P)) Y) :=
        epiQ _ _
      let _ : Epi (q X (smashUnit P) ▷ Y.right) :=
        epiQR X (smashUnit P) Y.right
      apply Under.UnderMorphism.ext
      apply (cancel_epi (q (((smash P hP).obj X).obj (smashUnit P)) Y)).1
      apply (cancel_epi (q X (smashUnit P) ▷ Y.right)).1
      simp only [Under.comp_right]
      slice_lhs 1 3 => rw [← Category.assoc,
        assoc_q X (smashUnit P) Y]
      slice_lhs 3 4 => rw [map_q (𝟙 X) (smashLeftUnitor P hP Y).hom]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp]
      slice_rhs 2 3 => rw [map_q (smashRightUnitor P hP X).hom (𝟙 Y)]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id]
      slice_rhs 1 2 => rw [← MonoidalCategory.comp_whiskerRight]
      exact core


theorem smashFactoryLaws :
    let smashMap : ∀ {A A' B B' : Under P},
      (A ⟶ A') → (B ⟶ B') →
        (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B') :=
      fun {_ _ B _} f g =>
        ((smash P hP).map f).app B ≫ ((smash P hP).obj _).map g
    ((∀ (X : Under P) {Y₁ Y₂ : Under P} (f : Y₁ ⟶ Y₂),
        smashMap (𝟙 X) f = ((smash P hP).obj X).map f) ∧
      (∀ {X₁ X₂ : Under P} (f : X₁ ⟶ X₂) (Y : Under P),
        smashMap f (𝟙 Y) = ((smash P hP).map f).app Y) ∧
      (∀ X Y : Under P,
        smashMap (𝟙 X) (𝟙 Y) = 𝟙 (((smash P hP).obj X).obj Y)) ∧
      (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Under P}
        (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
        (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        smashMap f₁ f₂ ≫ smashMap g₁ g₂ =
          smashMap (f₁ ≫ g₁) (f₂ ≫ g₂))) ∧
    ((∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Under P}
        (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        smashMap (smashMap f₁ f₂) f₃ ≫
            (smashAssociator P hP Y₁ Y₂ Y₃).hom =
          (smashAssociator P hP X₁ X₂ X₃).hom ≫
            smashMap f₁ (smashMap f₂ f₃)) ∧
      (∀ {X Y : Under P} (f : X ⟶ Y),
        smashMap (𝟙 (smashUnit P)) f ≫ (smashLeftUnitor P hP Y).hom =
          (smashLeftUnitor P hP X).hom ≫ f) ∧
      (∀ {X Y : Under P} (f : X ⟶ Y),
        smashMap f (𝟙 (smashUnit P)) ≫ (smashRightUnitor P hP Y).hom =
          (smashRightUnitor P hP X).hom ≫ f) ∧
      (∀ W X Y Z : Under P,
        smashMap (smashAssociator P hP W X Y).hom (𝟙 Z) ≫
              (smashAssociator P hP W (((smash P hP).obj X).obj Y) Z).hom ≫
            smashMap (𝟙 W) (smashAssociator P hP X Y Z).hom =
          (smashAssociator P hP (((smash P hP).obj W).obj X) Y Z).hom ≫
            (smashAssociator P hP W X (((smash P hP).obj Y).obj Z)).hom) ∧
      (∀ X Y : Under P,
        (smashAssociator P hP X (smashUnit P) Y).hom ≫
            smashMap (𝟙 X) (smashLeftUnitor P hP Y).hom =
          smashMap (smashRightUnitor P hP X).hom (𝟙 Y))) ∧
    ((∀ {X Y Z : Under P} (f : Y ⟶ Z),
        smashMap (𝟙 X) f ≫ (smashBraiding P hP X Z).hom =
          (smashBraiding P hP X Y).hom ≫ smashMap f (𝟙 X)) ∧
      (∀ {X Y : Under P} (f : X ⟶ Y) (Z : Under P),
        smashMap f (𝟙 Z) ≫ (smashBraiding P hP Y Z).hom =
          (smashBraiding P hP X Z).hom ≫ smashMap (𝟙 Z) f) ∧
      (∀ X Y Z : Under P,
        (smashAssociator P hP X Y Z).hom ≫
              (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
            (smashAssociator P hP Y Z X).hom =
          smashMap (smashBraiding P hP X Y).hom (𝟙 Z) ≫
              (smashAssociator P hP Y X Z).hom ≫
            smashMap (𝟙 Y) (smashBraiding P hP X Z).hom) ∧
      (∀ X Y Z : Under P,
        (smashAssociator P hP X Y Z).inv ≫
              (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
            (smashAssociator P hP Z X Y).inv =
          smashMap (𝟙 X) (smashBraiding P hP Y Z).hom ≫
              (smashAssociator P hP X Z Y).inv ≫
            smashMap (smashBraiding P hP X Z).hom (𝟙 Y)) ∧
      (∀ X Y : Under P,
        (smashBraiding P hP X Y).hom ≫
          (smashBraiding P hP Y X).hom = 𝟙 (((smash P hP).obj X).obj Y))) := by
  let smashMap : ∀ {A A' B B' : Under P},
      (A ⟶ A') → (B ⟶ B') →
        (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B') :=
    fun {_ _ B _} f g =>
      ((smash P hP).map f).app B ≫ ((smash P hP).obj _).map g
  let q (A B : Under P) :
      A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right :=
    (smashPresentation P hP A B).2.1.inl
  rcases smashMonoidalTensorLaws P hP with
    ⟨map_q, epiQ, epiQR, _epiQRR, _tensorHomDef,
      identityTensor, tensorComposition⟩
  have symmetricLaws := smashSymmetricLaws P hP smashMap q map_q epiQ epiQR
    (smashBraiding_hom_quotient P hP)
    (smashAssociator_hom_quotient P hP)
    (smashAssociator_inv_quotient P hP)
  rcases symmetricLaws with
    ⟨⟨braidingNaturalityRight, braidingNaturalityLeft⟩,
      ⟨⟨hexagonForward, hexagonReverse⟩, symmetry⟩⟩
  have idTensorHom : ∀ (X : Under P) {Y₁ Y₂ : Under P} (f : Y₁ ⟶ Y₂),
      smashMap (𝟙 X) f = ((smash P hP).obj X).map f := by
    intro X Y₁ Y₂ f
    dsimp only [smashMap]
    simp
  have tensorHomId : ∀ {X₁ X₂ : Under P} (f : X₁ ⟶ X₂) (Y : Under P),
      smashMap f (𝟙 Y) = ((smash P hP).map f).app Y := by
    intro X₁ X₂ f Y
    dsimp only [smashMap]
    simp
  exact
    ⟨⟨idTensorHom, tensorHomId, identityTensor, tensorComposition⟩,
      ⟨smashMonoidalAssociatorNaturality P hP,
        smashMonoidalLeftUnitorNaturality P hP,
        smashMonoidalRightUnitorNaturality P hP,
        smashMonoidalPentagon P hP,
        smashMonoidalTriangle P hP⟩,
      ⟨braidingNaturalityRight, braidingNaturalityLeft,
        hexagonForward, hexagonReverse, symmetry⟩⟩
-- Auxiliary formulas for the same monoidal construction.
where
  smashHexagon (P : C) (hP : IsTerminal P)
        (smashMap : ∀ {A A' B B' : Under P},
          (A ⟶ A') → (B ⟶ B') →
            (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
        (q : ∀ A B : Under P,
          A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right)
        (map_q : ∀ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B'),
          q A B ≫ (smashMap f g).right =
            (f.right ⊗ₘ g.right) ≫ q A' B')
        (epiQ : ∀ A B : Under P, Epi (q A B))
        (epiQR : ∀ (A B : Under P) (T : C), Epi (q A B ▷ T))
        (braid_q : ∀ A B : Under P,
          q A B ≫ (smashBraiding P hP A B).hom.right =
            (β_ A.right B.right).hom ≫ q B A)
        (assoc_hom_q : ∀ A B D : Under P,
          ((q A B ▷ D.right) ≫ q (((smash P hP).obj A).obj B) D) ≫
              (smashAssociator P hP A B D).hom.right =
            (α_ A.right B.right D.right).hom ≫
              (A.right ◁ q B D) ≫ q A (((smash P hP).obj B).obj D))
        (assoc_inv_q : ∀ A B D : Under P,
          ((A.right ◁ q B D) ≫ q A (((smash P hP).obj B).obj D)) ≫
              (smashAssociator P hP A B D).inv.right =
            (α_ A.right B.right D.right).inv ≫
              (q A B ▷ D.right) ≫ q (((smash P hP).obj A).obj B) D)
        (X Y Z : Under P) :
        ((smashAssociator P hP X Y Z).hom ≫
            (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
            (smashAssociator P hP Y Z X).hom =
          smashMap (smashBraiding P hP X Y).hom (𝟙 Z) ≫
            (smashAssociator P hP Y X Z).hom ≫
            smashMap (𝟙 Y) (smashBraiding P hP X Z).hom) ∧
        ((smashAssociator P hP X Y Z).inv ≫
            (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
            (smashAssociator P hP Z X Y).inv =
          smashMap (𝟙 X) (smashBraiding P hP Y Z).hom ≫
            (smashAssociator P hP X Z Y).inv ≫
            smashMap (smashBraiding P hP X Z).hom (𝟙 Y)) := by
      have aqh := assoc_hom_q
      have aqi := assoc_inv_q
      have cq := braid_q
      let mq {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B') :=
        map_q f g
      have epiQL (A B : Under P) (T : C) : Epi (T ◁ q A B) := by
        have h : T ◁ q A B =
            (β_ T (A.right ⊗ B.right)).hom ≫ (q A B ▷ T) ≫
              (β_ T (((smash P hP).obj A).obj B).right).inv := by
          apply (cancel_mono
            (β_ T (((smash P hP).obj A).obj B).right).hom).1
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          exact BraidedCategory.braiding_naturality_right T (q A B)
        rw [h]
        let _ : Epi (q A B ▷ T) := epiQR A B T
        infer_instance
      constructor
      · let qL := (q X Y ▷ Z.right) ≫ q (((smash P hP).obj X).obj Y) Z
        let qR := (Y.right ◁ q Z X) ≫ q Y (((smash P hP).obj Z).obj X)
        have hL : qL ≫ ((smashAssociator P hP X Y Z).hom ≫
              (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
              (smashAssociator P hP Y Z X).hom).right =
            (α_ X.right Y.right Z.right).hom ≫
              (β_ X.right (Y.right ⊗ Z.right)).hom ≫
              (α_ Y.right Z.right X.right).hom ≫ qR := by
          dsimp only [qL, qR]
          simp only [Under.comp_right, Category.assoc]
          slice_lhs 1 3 => rw [← Category.assoc, aqh]
          slice_lhs 3 4 => rw [cq]
          slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality_right]
          slice_lhs 3 5 => rw [← Category.assoc, aqh]
        let qLYXZ := (q Y X ▷ Z.right) ≫ q (((smash P hP).obj Y).obj X) Z
        have hR1 : qL ≫ (smashMap (smashBraiding P hP X Y).hom (𝟙 Z)).right =
            ((β_ X.right Y.right).hom ▷ Z.right) ≫ qLYXZ := by
          dsimp only [qL]
          simp only [Category.assoc]
          slice_lhs 2 3 => rw [mq]
          simp only [Under.id_right, MonoidalCategory.tensorHom_id]
          slice_lhs 1 2 =>
            rw [← MonoidalCategory.comp_whiskerRight, cq,
              MonoidalCategory.comp_whiskerRight]
          dsimp only [qLYXZ]
          exact Category.assoc _ _ _
        have hR2 : qLYXZ ≫ ((smashAssociator P hP Y X Z).hom ≫
              smashMap (𝟙 Y) (smashBraiding P hP X Z).hom).right =
            (α_ Y.right X.right Z.right).hom ≫
              (Y.right ◁ (β_ X.right Z.right).hom) ≫ qR := by
          dsimp only [qLYXZ, qR]
          simp only [Under.comp_right, Category.assoc]
          slice_lhs 1 3 => rw [← Category.assoc, aqh]
          slice_lhs 3 4 => rw [mq]
          simp only [Under.id_right, MonoidalCategory.id_tensorHom]
          slice_lhs 2 3 =>
            rw [← MonoidalCategory.whiskerLeft_comp, cq,
              MonoidalCategory.whiskerLeft_comp]
          simp only [Category.assoc]
        have hR : qL ≫ (smashMap (smashBraiding P hP X Y).hom (𝟙 Z) ≫
              (smashAssociator P hP Y X Z).hom ≫
              smashMap (𝟙 Y) (smashBraiding P hP X Z).hom).right =
            ((β_ X.right Y.right).hom ▷ Z.right) ≫
              (α_ Y.right X.right Z.right).hom ≫
              (Y.right ◁ (β_ X.right Z.right).hom) ≫ qR := by
          change qL ≫ (smashMap (smashBraiding P hP X Y).hom (𝟙 Z)).right ≫
              ((smashAssociator P hP Y X Z).hom ≫
                smashMap (𝟙 Y) (smashBraiding P hP X Z).hom).right = _
          rw [← Category.assoc, hR1, Category.assoc, hR2]
        apply Under.UnderMorphism.ext
        let _ : Epi (q (((smash P hP).obj X).obj Y) Z) := epiQ _ _
        let _ : Epi (q X Y ▷ Z.right) := epiQR X Y Z.right
        apply (cancel_epi (q (((smash P hP).obj X).obj Y) Z)).1
        apply (cancel_epi (q X Y ▷ Z.right)).1
        have hh : qL ≫ ((smashAssociator P hP X Y Z).hom ≫
              (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
              (smashAssociator P hP Y Z X).hom).right =
            qL ≫ (smashMap (smashBraiding P hP X Y).hom (𝟙 Z) ≫
              (smashAssociator P hP Y X Z).hom ≫
              smashMap (𝟙 Y) (smashBraiding P hP X Z).hom).right := by
          rw [hL, hR]
          simpa only [Category.assoc, qR] using congrArg (fun k => k ≫ qR)
            (BraidedCategory.hexagon_forward X.right Y.right Z.right)
        simpa only [qL, Under.comp_right, Category.assoc] using hh
      · let qR := (X.right ◁ q Y Z) ≫ q X (((smash P hP).obj Y).obj Z)
        let qL := (q Z X ▷ Y.right) ≫ q (((smash P hP).obj Z).obj X) Y
        have hL : qR ≫ ((smashAssociator P hP X Y Z).inv ≫
              (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
              (smashAssociator P hP Z X Y).inv).right =
            (α_ X.right Y.right Z.right).inv ≫
              (β_ (X.right ⊗ Y.right) Z.right).hom ≫
              (α_ Z.right X.right Y.right).inv ≫ qL := by
          dsimp only [qR, qL]
          simp only [Under.comp_right, Category.assoc]
          slice_lhs 1 3 => rw [← Category.assoc, aqi]
          slice_lhs 3 4 => rw [cq]
          slice_lhs 2 3 => rw [BraidedCategory.braiding_naturality_left]
          slice_lhs 3 5 => rw [← Category.assoc, aqi]
        let qRXZY := (X.right ◁ q Z Y) ≫ q X (((smash P hP).obj Z).obj Y)
        have hR1 : qR ≫ (smashMap (𝟙 X) (smashBraiding P hP Y Z).hom).right =
            (X.right ◁ (β_ Y.right Z.right).hom) ≫ qRXZY := by
          dsimp only [qR, qRXZY]
          simp only [Category.assoc]
          slice_lhs 2 3 => rw [mq]
          simp only [Under.id_right, MonoidalCategory.id_tensorHom]
          slice_lhs 1 2 =>
            rw [← MonoidalCategory.whiskerLeft_comp, cq,
              MonoidalCategory.whiskerLeft_comp]
          simp only [Category.assoc]
        have hR2 : qRXZY ≫ ((smashAssociator P hP X Z Y).inv ≫
              smashMap (smashBraiding P hP X Z).hom (𝟙 Y)).right =
            (α_ X.right Z.right Y.right).inv ≫
              ((β_ X.right Z.right).hom ▷ Y.right) ≫ qL := by
          dsimp only [qRXZY, qL]
          simp only [Under.comp_right, Category.assoc]
          slice_lhs 1 3 => rw [← Category.assoc, aqi]
          slice_lhs 3 4 => rw [mq]
          simp only [Under.id_right, MonoidalCategory.tensorHom_id]
          slice_lhs 2 3 =>
            rw [← MonoidalCategory.comp_whiskerRight, cq,
              MonoidalCategory.comp_whiskerRight]
          simp only [Category.assoc]
        have hR : qR ≫ (smashMap (𝟙 X) (smashBraiding P hP Y Z).hom ≫
              (smashAssociator P hP X Z Y).inv ≫
              smashMap (smashBraiding P hP X Z).hom (𝟙 Y)).right =
            (X.right ◁ (β_ Y.right Z.right).hom) ≫
              (α_ X.right Z.right Y.right).inv ≫
              ((β_ X.right Z.right).hom ▷ Y.right) ≫ qL := by
          change qR ≫ (smashMap (𝟙 X) (smashBraiding P hP Y Z).hom).right ≫
              ((smashAssociator P hP X Z Y).inv ≫
                smashMap (smashBraiding P hP X Z).hom (𝟙 Y)).right = _
          rw [← Category.assoc, hR1, Category.assoc, hR2]
        apply Under.UnderMorphism.ext
        let _ : Epi (q X (((smash P hP).obj Y).obj Z)) := epiQ _ _
        let _ : Epi (X.right ◁ q Y Z) := epiQL Y Z X.right
        apply (cancel_epi (q X (((smash P hP).obj Y).obj Z))).1
        apply (cancel_epi (X.right ◁ q Y Z)).1
        have hh : qR ≫ ((smashAssociator P hP X Y Z).inv ≫
              (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
              (smashAssociator P hP Z X Y).inv).right =
            qR ≫ (smashMap (𝟙 X) (smashBraiding P hP Y Z).hom ≫
              (smashAssociator P hP X Z Y).inv ≫
              smashMap (smashBraiding P hP X Z).hom (𝟙 Y)).right := by
          rw [hL, hR]
          simpa only [Category.assoc, qL] using congrArg (fun k => k ≫ qL)
            (BraidedCategory.hexagon_reverse X.right Y.right Z.right)
        simpa only [qR, Under.comp_right, Category.assoc] using hh
  -- The same smash maps satisfy symmetry coherence.
  smashSymmetricLaws (P : C) (hP : IsTerminal P)
      (smashMap : ∀ {A A' B B' : Under P},
        (A ⟶ A') → (B ⟶ B') →
          (((smash P hP).obj A).obj B ⟶ ((smash P hP).obj A').obj B'))
      (q : ∀ A B : Under P,
        A.right ⊗ B.right ⟶ (((smash P hP).obj A).obj B).right)
      (map_q : ∀ {A A' B B' : Under P} (f : A ⟶ A') (g : B ⟶ B'),
        q A B ≫ (smashMap f g).right =
          (f.right ⊗ₘ g.right) ≫ q A' B')
      (epiQ : ∀ A B : Under P, Epi (q A B))
      (epiQR : ∀ (A B : Under P) (T : C), Epi (q A B ▷ T))
      (braid_q : ∀ A B : Under P,
        q A B ≫ (smashBraiding P hP A B).hom.right =
          (β_ A.right B.right).hom ≫ q B A)
      (assoc_hom_q : ∀ A B D : Under P,
        ((q A B ▷ D.right) ≫ q (((smash P hP).obj A).obj B) D) ≫
            (smashAssociator P hP A B D).hom.right =
          (α_ A.right B.right D.right).hom ≫
            (A.right ◁ q B D) ≫ q A (((smash P hP).obj B).obj D))
      (assoc_inv_q : ∀ A B D : Under P,
        ((A.right ◁ q B D) ≫ q A (((smash P hP).obj B).obj D)) ≫
            (smashAssociator P hP A B D).inv.right =
          (α_ A.right B.right D.right).inv ≫
            (q A B ▷ D.right) ≫ q (((smash P hP).obj A).obj B) D) :
      ((∀ {X Y Z : Under P} (f : Y ⟶ Z),
          smashMap (𝟙 X) f ≫ (smashBraiding P hP X Z).hom =
            (smashBraiding P hP X Y).hom ≫ smashMap f (𝟙 X)) ∧
        (∀ {X Y : Under P} (f : X ⟶ Y) (Z : Under P),
          smashMap f (𝟙 Z) ≫ (smashBraiding P hP Y Z).hom =
            (smashBraiding P hP X Z).hom ≫ smashMap (𝟙 Z) f)) ∧
      (((∀ X Y Z : Under P,
          (smashAssociator P hP X Y Z).hom ≫
              (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
              (smashAssociator P hP Y Z X).hom =
            smashMap (smashBraiding P hP X Y).hom (𝟙 Z) ≫
              (smashAssociator P hP Y X Z).hom ≫
              smashMap (𝟙 Y) (smashBraiding P hP X Z).hom) ∧
        (∀ X Y Z : Under P,
          (smashAssociator P hP X Y Z).inv ≫
              (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
              (smashAssociator P hP Z X Y).inv =
            smashMap (𝟙 X) (smashBraiding P hP Y Z).hom ≫
              (smashAssociator P hP X Z Y).inv ≫
              smashMap (smashBraiding P hP X Z).hom (𝟙 Y))) ∧
        (∀ X Y : Under P,
          (smashBraiding P hP X Y).hom ≫
            (smashBraiding P hP Y X).hom = 𝟙 _)) := by
    have braidNatRight {X Y Z : Under P} (f : Y ⟶ Z) :
        smashMap (𝟙 X) f ≫ (smashBraiding P hP X Z).hom =
          (smashBraiding P hP X Y).hom ≫ smashMap f (𝟙 X) := by
      apply Under.UnderMorphism.ext
      let _ : Epi (q X Y) := epiQ X Y
      apply (cancel_epi (q X Y)).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      slice_lhs 2 3 => rw [braid_q]
      slice_rhs 1 2 => rw [braid_q]
      slice_rhs 2 3 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ q Z X)
        (BraidedCategory.braiding_naturality_right X.right f.right)
    have braidNatLeft {X Y : Under P} (f : X ⟶ Y) (Z : Under P) :
        smashMap f (𝟙 Z) ≫ (smashBraiding P hP Y Z).hom =
          (smashBraiding P hP X Z).hom ≫ smashMap (𝟙 Z) f := by
      apply Under.UnderMorphism.ext
      let _ : Epi (q X Z) := epiQ X Z
      apply (cancel_epi (q X Z)).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.tensorHom_id]
      slice_lhs 2 3 => rw [braid_q]
      slice_rhs 1 2 => rw [braid_q]
      slice_rhs 2 3 => rw [map_q]
      simp only [Under.id_right, MonoidalCategory.id_tensorHom]
      simpa only [Category.assoc] using congrArg (fun k => k ≫ q Z Y)
        (BraidedCategory.braiding_naturality_left f.right Z.right)
    have hexagonForward (X Y Z : Under P) :=
      (smashHexagon P hP smashMap q map_q epiQ epiQR braid_q
        assoc_hom_q assoc_inv_q X Y Z).1
    have hexagonReverse (X Y Z : Under P) :=
      (smashHexagon P hP smashMap q map_q epiQ epiQR braid_q
        assoc_hom_q assoc_inv_q X Y Z).2
    have symmetry (X Y : Under P) :
        (smashBraiding P hP X Y).hom ≫
          (smashBraiding P hP Y X).hom = 𝟙 _ := by
      apply Under.UnderMorphism.ext
      let _ : Epi (q X Y) := epiQ X Y
      apply (cancel_epi (q X Y)).1
      simp only [Under.comp_right]
      slice_lhs 1 2 => rw [braid_q]
      slice_lhs 2 3 => rw [braid_q]
      simp only [Under.id_right]
      rw [Category.comp_id]
      simpa only [Category.assoc, Category.id_comp] using congrArg
        (fun k => k ≫ q X Y) (SymmetricCategory.symmetry X.right Y.right)
    exact ⟨⟨braidNatRight, braidNatLeft⟩,
      ⟨⟨hexagonForward, hexagonReverse⟩, symmetry⟩⟩

/-- The smash product gives an explicit monoidal factory on objects under `P`. -/
noncomputable abbrev smashMonoidalCategory :
    MonoidalCategory (Under P) := by
  let ops : MonoidalCategoryStruct (Under P) :=
    { tensorObj := fun X Y => ((smash P hP).obj X).obj Y
      whiskerLeft := fun X {_ _} f => ((smash P hP).obj X).map f
      whiskerRight := fun {_ _} f Y => ((smash P hP).map f).app Y
      tensorHom := fun {_ _ B _} f g =>
        ((smash P hP).map f).app B ≫ ((smash P hP).obj _).map g
      tensorUnit := smashUnit P
      associator := smashAssociator P hP
      leftUnitor := smashLeftUnitor P hP
      rightUnitor := smashRightUnitor P hP }
  let laws := smashFactoryLaws P hP
  exact
    { (@MonoidalCategory.ofTensorHom (Under P) _ ops
        (id_tensorHom_id := laws.1.2.2.1)
        (id_tensorHom := laws.1.1)
        (tensorHom_id := laws.1.2.1)
        (tensorHom_comp_tensorHom := laws.1.2.2.2)
        (associator_naturality := laws.2.1.1)
        (leftUnitor_naturality := laws.2.1.2.1)
        (rightUnitor_naturality := laws.2.1.2.2.1)
        (pentagon := laws.2.1.2.2.2.1)
        (triangle := laws.2.1.2.2.2.2)) with
      toMonoidalCategoryStruct := ops }

/-- The generic smash quotient is natural in both pointed inputs. -/
theorem smashQuotient_naturality
    {X X' Y Y' : Under P} (f : X ⟶ X') (g : Y ⟶ Y') :
    (smashPresentation P hP X Y).2.1.inl ≫
        (@MonoidalCategory.tensorHom (Under P) _
          (smashMonoidalCategory P hP).toMonoidalCategoryStruct
          X X' Y Y' f g).right =
      (f.right ⊗ₘ g.right) ≫
        (smashPresentation P hP X' Y').2.1.inl := by
  change (smashPresentation P hP X Y).2.1.inl ≫
      ((((smash P hP).map f).app Y ≫
        ((smash P hP).obj X').map g).right) =
    (f.right ⊗ₘ g.right) ≫
      (smashPresentation P hP X' Y').2.1.inl
  exact (smashMonoidalTensorLaws P hP).1 f g

/-- The intrinsic smash braiding is symmetric. -/
noncomputable abbrev smashSymmetricCategory :
    @SymmetricCategory (Under P) _ (smashMonoidalCategory P hP) := by
  let laws := smashFactoryLaws P hP
  exact
    @SymmetricCategory.mk (Under P) _ (smashMonoidalCategory P hP)
      (@BraidedCategory.mk (Under P) _ (smashMonoidalCategory P hP)
        (fun X Y => smashBraiding P hP X Y)
        (by
          intro X Y Z f
          change ((smash P hP).obj X).map f ≫
              (smashBraiding P hP X Z).hom =
            (smashBraiding P hP X Y).hom ≫ ((smash P hP).map f).app X
          simpa only [laws.1.1, laws.1.2.1] using laws.2.2.1 f)
        (by
          intro X Y f Z
          change ((smash P hP).map f).app Z ≫
              (smashBraiding P hP Y Z).hom =
            (smashBraiding P hP X Z).hom ≫ ((smash P hP).obj Z).map f
          simpa only [laws.1.1, laws.1.2.1] using laws.2.2.2.1 f Z)
        (by
          intro X Y Z
          change (smashAssociator P hP X Y Z).hom ≫
                (smashBraiding P hP X (((smash P hP).obj Y).obj Z)).hom ≫
              (smashAssociator P hP Y Z X).hom =
            ((smash P hP).map (smashBraiding P hP X Y).hom).app Z ≫
                (smashAssociator P hP Y X Z).hom ≫
              ((smash P hP).obj Y).map (smashBraiding P hP X Z).hom
          simpa only [laws.1.1, laws.1.2.1] using laws.2.2.2.2.1 X Y Z)
        (by
          intro X Y Z
          change (smashAssociator P hP X Y Z).inv ≫
                (smashBraiding P hP (((smash P hP).obj X).obj Y) Z).hom ≫
              (smashAssociator P hP Z X Y).inv =
            ((smash P hP).obj X).map (smashBraiding P hP Y Z).hom ≫
                (smashAssociator P hP X Z Y).inv ≫
              ((smash P hP).map (smashBraiding P hP X Z).hom).app Y
          simpa only [laws.1.1, laws.1.2.1] using laws.2.2.2.2.2.1 X Y Z))
      (by
        intro X Y
        change (smashBraiding P hP X Y).hom ≫
          (smashBraiding P hP Y X).hom =
            𝟙 (((smash P hP).obj X).obj Y)
        exact laws.2.2.2.2.2.2 X Y)

end CategoryTheory.Pointed
