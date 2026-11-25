/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Basic.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Comma.Over.Basic

import Mathlib.CategoryTheory.Whiskering

/-!
# Pointed simplicial sets

A pointed simplicial set is an object of the native undercategory of the standard
zero-simplex. Evaluating its pointing gives a point in every degree, preserved by
all simplicial operators. Conversely, the points of a simplicial object in
`Pointed` define a map from the zero-simplex. These constructions give an explicit
equivalence, allowing based simplicial constructions to use either presentation.
-/

public section

universe u

open CategoryTheory CategoryTheory.ConcreteCategory Simplicial

namespace MathlibExt.SpectraSource

/-- Simplicial sets with a chosen point, using the native undercategory. -/
abbrev PointedSSet := Under (Δ[0] : SSet.{u})

namespace PointedSSet

/-- The chosen simplex in each degree of a pointed simplicial set. -/
def point (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) : X.right.obj n :=
  X.hom.app n (SSet.stdSimplex.const 0 0 n)

@[simp]
lemma point_mk {X : SSet.{u}} (p : Δ[0] ⟶ X) (n : SimplexCategoryᵒᵖ) :
    point (Under.mk p) n = p.app n (SSet.stdSimplex.const 0 0 n) := (rfl)

@[simp]
lemma hom_app (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) (x : Δ[0].obj n) :
    X.hom.app n x = X.point n := by
  congr 1
  exact SSet.stdSimplex.objEquiv.injective (Subsingleton.elim _ _)

@[simp]
lemma map_point (X : PointedSSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    X.right.map f (X.point n) = X.point m := by
  simpa only [types_comp_apply, hom_app] using (congr_hom (X.hom.naturality f)
    (SSet.stdSimplex.const 0 0 n)).symm

@[simp]
lemma app_point {X Y : PointedSSet.{u}} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    f.right.app n (X.point n) = Y.point n := by
  simpa only [NatTrans.comp_app, types_comp_apply, hom_app] using
    congr_hom (congr_app (Under.w f) n) (SSet.stdSimplex.const 0 0 n)

/-- A composite of based maps acts on simplices as the composite of the two functions. This is not
a `simp` lemma, since `simp` unfolds the composite through `Under.comp_right` and
`NatTrans.comp_app`; it gives that unfolding in one rewrite. -/
lemma comp_right_app_apply {X Y Z : PointedSSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : SimplexCategoryᵒᵖ) (x : X.right.obj n) :
    (f ≫ g).right.app n x = g.right.app n (f.right.app n x) := (rfl)

/-- Evaluate a pointed simplicial set as a simplicial object in pointed types. -/
def toSimplicialPointed : PointedSSet.{u} ⥤ SimplicialObject Pointed.{u} where
  obj X :=
    { obj n := Pointed.of (X.point n)
      map f := ⟨X.right.map f, X.map_point f⟩
      map_id n := Pointed.Hom.ext (by funext x; exact congr_hom (X.right.map_id n) x)
      map_comp f g := Pointed.Hom.ext (by
        funext x
        exact congr_hom (X.right.map_comp f g) x) }
  map f :=
    { app n := ⟨f.right.app n, app_point f n⟩
      naturality n m g := Pointed.Hom.ext (by
        funext x
        exact congr_hom (f.right.naturality g) x) }

/-- Recover a pointed simplicial set from its compatible degreewise points. -/
def fromSimplicialPointed : SimplicialObject Pointed.{u} ⥤ PointedSSet.{u} where
  -- Fix the underlying functor to the native forgetful image.
  obj X := Under.mk (show Δ[0] ⟶ X ⋙ forget Pointed from
    { app n := ↾(fun _ ↦ (X.obj n).point)
      naturality n m f := by
        ext _
        exact ((X.map f).map_point).symm })
  map f := Under.homMk (CategoryTheory.Functor.whiskerRight f (forget Pointed)) (by
    ext n _
    exact (f.app n).map_point)

@[simp]
lemma toSimplicialPointed_obj_obj (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSimplicialPointed.obj X).obj n = Pointed.of (X.point n) := (rfl)

@[simp]
lemma fromSimplicialPointed_obj_right (X : SimplicialObject Pointed.{u}) :
    (fromSimplicialPointed.obj X).right = X ⋙ forget Pointed := (rfl)

/-- Forgetting degreewise points agrees naturally with forgetting the chosen pointing. -/
def forgetIso :
    toSimplicialPointed ⋙ (SimplicialObject.whiskering _ _).obj (forget Pointed.{u}) ≅
      Under.forget (Δ[0] : SSet.{u}) :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (by intros; ext n x; rfl)

lemma forgetIso_hom_app_app (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (forgetIso.hom.app X).app n = eqToHom (by simp) := (rfl)

lemma forgetIso_inv_app_app (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (forgetIso.inv.app X).app n = eqToHom (by simp) := (rfl)

@[simp↓]
lemma forgetIso_hom_app_point (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (forgetIso.hom.app X).app n ((toSimplicialPointed.obj X).obj n).point =
      X.point n := (rfl)

/-- The forward construction applies each simplicial operator to the underlying simplex. -/
lemma toSimplicialPointed_obj_map (X : PointedSSet.{u})
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (toSimplicialPointed.obj X).obj n) :
    (forgetIso.hom.app X).app m (((toSimplicialPointed.obj X).map f).toFun x) =
      X.right.map f ((forgetIso.hom.app X).app n x) := (rfl)

/-- The forward construction applies each based map to the underlying simplex. -/
lemma toSimplicialPointed_map_app {X Y : PointedSSet.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (x : (toSimplicialPointed.obj X).obj n) :
    (forgetIso.hom.app Y).app n ((toSimplicialPointed.map f |>.app n).toFun x) =
      f.right.app n ((forgetIso.hom.app X).app n x) := (rfl)

/-- The underlying simplicial set of the inverse construction is the forgetful image. -/
def fromForgetIso :
    fromSimplicialPointed ⋙ Under.forget (Δ[0] : SSet.{u}) ≅
      (SimplicialObject.whiskering _ _).obj (forget Pointed.{u}) :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (by intros; ext n x; rfl)

lemma fromForgetIso_hom_app_app (X : SimplicialObject Pointed.{u})
    (n : SimplexCategoryᵒᵖ) :
    (fromForgetIso.hom.app X).app n = eqToHom (by simp) := (rfl)

lemma fromForgetIso_inv_app_app (X : SimplicialObject Pointed.{u})
    (n : SimplexCategoryᵒᵖ) :
    (fromForgetIso.inv.app X).app n = eqToHom (by simp) := (rfl)

@[simp↓]
lemma fromForgetIso_hom_app_point (X : SimplicialObject Pointed.{u})
    (n : SimplexCategoryᵒᵖ) :
    (fromForgetIso.hom.app X).app n ((fromSimplicialPointed.obj X).point n) =
      (X.obj n).point := (rfl)

/-- The inverse construction acts by the original degreewise pointed map. -/
lemma fromSimplicialPointed_map_app {X Y : SimplicialObject Pointed.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (x : (fromSimplicialPointed.obj X).right.obj n) :
    (fromForgetIso.hom.app Y).app n ((fromSimplicialPointed.map f).right.app n x) =
      (f.app n).toFun ((fromForgetIso.hom.app X).app n x) := (rfl)

/-- The conversion back to a pointed simplicial set preserves every simplex. -/
def unitIso : 𝟭 PointedSSet.{u} ≅ toSimplicialPointed ⋙ fromSimplicialPointed :=
  NatIso.ofComponents (fun X ↦ Under.isoMk (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    (by ext n x; exact X.hom_app n x)) (by intros; ext n x; rfl)

/-- The degreewise pointed presentation is recovered by the identity maps. -/
def counitIso : fromSimplicialPointed ⋙ toSimplicialPointed ≅
    𝟭 (SimplicialObject Pointed.{u}) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun n ↦ Pointed.Iso.mk (Equiv.refl _) rfl)) (by intros; ext n x; rfl)

lemma unitIso_hom_app_right_app (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (unitIso.hom.app X).right.app n = eqToHom (by simp) := (rfl)

lemma unitIso_inv_app_right_app (X : PointedSSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (unitIso.inv.app X).right.app n = eqToHom (by simp) := (rfl)

lemma counitIso_hom_app_app (X : SimplicialObject Pointed.{u}) (n : SimplexCategoryᵒᵖ) :
    (forget Pointed).map (counitIso.hom.app X |>.app n) = eqToHom (by
      simp only [Functor.comp_obj, Functor.id_obj, toSimplicialPointed_obj_obj]
      exact congrArg (fun Y : SSet ↦ Y.obj n) (fromSimplicialPointed_obj_right X)) := (rfl)

lemma counitIso_inv_app_app (X : SimplicialObject Pointed.{u}) (n : SimplexCategoryᵒᵖ) :
    (forget Pointed).map (counitIso.inv.app X |>.app n) = eqToHom (by
      simp only [Functor.comp_obj, Functor.id_obj, toSimplicialPointed_obj_obj]
      exact (congrArg (fun Y : SSet ↦ Y.obj n) (fromSimplicialPointed_obj_right X)).symm) := (rfl)

/-- The equivalence between native pointed simplicial sets and simplicial pointed types. -/
def simplicialPointedEquivalence : PointedSSet.{u} ≌ SimplicialObject Pointed.{u} where
  functor := toSimplicialPointed
  inverse := fromSimplicialPointed
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp X := by ext n x; rfl

@[simp]
lemma simplicialPointedEquivalence_functor :
    simplicialPointedEquivalence.{u}.functor = toSimplicialPointed := (rfl)

@[simp]
lemma simplicialPointedEquivalence_inverse :
    simplicialPointedEquivalence.{u}.inverse = fromSimplicialPointed := (rfl)

end PointedSSet

end MathlibExt.SpectraSource
