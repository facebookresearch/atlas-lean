/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData
public import MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
Transports simplicial data to genuine simplicial objects.

`Data C` packages degree objects with face and degeneracy maps satisfying the
six simplicial identities. `toSimplicialObject` precomposes `X.toGenRelFunctor`
with the opposite of the explicit canonical-object inverse
`SimplexCategoryGenRel.fromSimplexCategory`, and `toSimplicialFunctor` packages
this functorially in `Data` morphisms. Degree `n` is definitionally `X.obj n`;
faces and degeneracies compute to `X.δ` and `X.σ`.

Orientation: the transport uses the canonical inverse (`Δ ↦ mk Δ.len`), not the
opaque `asEquivalence` quasi-inverse, so no unit/counit transport enters the
computation lemmas. This file only performs the transport; the
generators-relations presentation comparison itself lives elsewhere.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u v' u'

namespace CategoryTheory

namespace SimplicialObject

namespace Data

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/--
Transport `Data C` to a simplicial object via the explicit canonical inverse
`SimplexCategoryGenRel.fromSimplexCategory.op`.
-/
noncomputable def toSimplicialObject (X : Data C) : SimplicialObject C :=
  SimplexCategoryGenRel.fromSimplexCategory.op ⋙ X.toGenRelFunctor

@[simp]
theorem toSimplicialObject_obj_mk (X : Data C) (n : ℕ) :
    X.toSimplicialObject.obj (op (SimplexCategory.mk n)) = X.obj n :=
  rfl

theorem toSimplicialObject_obj (X : Data C) (Δ : SimplexCategoryᵒᵖ) :
    X.toSimplicialObject.obj Δ = X.obj (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

theorem toSimplicialObject_map_δ (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    X.toSimplicialObject.map (SimplexCategory.δ i).op = X.δ i := by
  change X.toGenRelFunctor.map
      (SimplexCategoryGenRel.fromSimplexCategory.op.map (SimplexCategory.δ i).op) = X.δ i
  have h_op : SimplexCategoryGenRel.fromSimplexCategory.op.map (SimplexCategory.δ i).op =
      (SimplexCategoryGenRel.δ i).op := by
    apply Quiver.Hom.unop_inj
    change SimplexCategoryGenRel.fromSimplexCategory.map (SimplexCategory.δ i) =
      SimplexCategoryGenRel.δ i
    exact SimplexCategoryGenRel.fromSimplexCategory_map_δ i
  rw [h_op]
  exact X.toGenRelFunctor_map_δ_op i

theorem toSimplicialObject_map_σ (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    X.toSimplicialObject.map (SimplexCategory.σ i).op = X.σ i := by
  change X.toGenRelFunctor.map
      (SimplexCategoryGenRel.fromSimplexCategory.op.map (SimplexCategory.σ i).op) = X.σ i
  have h_op : SimplexCategoryGenRel.fromSimplexCategory.op.map (SimplexCategory.σ i).op =
      (SimplexCategoryGenRel.σ i).op := by
    apply Quiver.Hom.unop_inj
    change SimplexCategoryGenRel.fromSimplexCategory.map (SimplexCategory.σ i) =
      SimplexCategoryGenRel.σ i
    exact SimplexCategoryGenRel.fromSimplexCategory_map_σ i
  rw [h_op]
  exact X.toGenRelFunctor_map_σ_op i

/-- Induced morphism of simplicial objects by left-whiskering `toGenRelNatTrans`. -/
noncomputable def toSimplicialNatTrans {X Y : Data C} (f : X ⟶ Y) :
    X.toSimplicialObject ⟶ Y.toSimplicialObject :=
  Functor.whiskerLeft SimplexCategoryGenRel.fromSimplexCategory.op (toGenRelNatTrans f)

@[simp]
theorem toSimplicialNatTrans_app_mk {X Y : Data C} (f : X ⟶ Y) (n : ℕ) :
    (toSimplicialNatTrans f).app (op (SimplexCategory.mk n)) = f.app n :=
  rfl

theorem toSimplicialNatTrans_app {X Y : Data C} (f : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialNatTrans f).app Δ = f.app (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

/-- Functorial packaging `Data C ⥤ SimplicialObject C`. -/
noncomputable def toSimplicialFunctor : Data C ⥤ SimplicialObject C where
  obj X := X.toSimplicialObject
  map f := toSimplicialNatTrans f
  map_id X := by
    ext Δ
    obtain ⟨Δ⟩ := Δ
    rfl
  map_comp f g := by
    ext Δ
    obtain ⟨Δ⟩ := Δ
    rfl

@[simp]
theorem toSimplicialFunctor_obj_obj_mk (X : Data C) (n : ℕ) :
    (toSimplicialFunctor (C := C).obj X).obj (op (SimplexCategory.mk n)) = X.obj n :=
  rfl

theorem toSimplicialFunctor_obj_obj (X : Data C) (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialFunctor (C := C).obj X).obj Δ = X.obj (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem toSimplicialFunctor_map_app_mk {X Y : Data C} (f : X ⟶ Y) (n : ℕ) :
    (toSimplicialFunctor (C := C).map f).app (op (SimplexCategory.mk n)) = f.app n :=
  rfl

theorem toSimplicialFunctor_map_app {X Y : Data C} (f : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialFunctor (C := C).map f).app Δ = f.app (unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem toSimplicialFunctor_obj_map_δ (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    (toSimplicialFunctor (C := C).obj X).map (SimplexCategory.δ i).op = X.δ i :=
  toSimplicialObject_map_δ X i

@[simp]
theorem toSimplicialFunctor_obj_map_σ (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    (toSimplicialFunctor (C := C).obj X).map (SimplexCategory.σ i).op = X.σ i :=
  toSimplicialObject_map_σ X i

/-- GenRel δ-generator comparison for postcomposition. -/
private theorem toGenRelFunctor_mapObj_map_δ_op (F : C ⥤ D) (X : Data C) {n : ℕ}
    (i : Fin (n + 2)) :
    (mapObj F X).toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op =
      F.map (X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op) := by
  simp only [toGenRelFunctor_map_δ_op, mapObj_δ]
  rfl

/-- GenRel σ-generator comparison for postcomposition. -/
private theorem toGenRelFunctor_mapObj_map_σ_op (F : C ⥤ D) (X : Data C) {n : ℕ}
    (i : Fin (n + 1)) :
    (mapObj F X).toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op =
      F.map (X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op) := by
  simp only [toGenRelFunctor_map_σ_op, mapObj_σ]
  rfl

/--
Arbitrary GenRel morphism comparison for postcomposition, by generator
induction using `Functor.map_comp`.
-/
private theorem toGenRelFunctor_mapObj_map_op (F : C ⥤ D) (X : Data C)
    {a b : SimplexCategoryGenRel} (f : a ⟶ b) :
    (mapObj F X).toGenRelFunctor.map f.op =
      F.map (X.toGenRelFunctor.map f.op) := by
  induction f using SimplexCategoryGenRel.hom_induction with
  | id => simp
  | comp_δ u i ih =>
    have hX : X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op =
        X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          X.toGenRelFunctor.map u.op := by
      rw [op_comp, Functor.map_comp]
    have hM : (mapObj F X).toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op =
        (mapObj F X).toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          (mapObj F X).toGenRelFunctor.map u.op := by
      rw [op_comp, Functor.map_comp]
    rw [hM, hX, F.map_comp, toGenRelFunctor_mapObj_map_δ_op, ih]
    rfl
  | comp_σ u i ih =>
    have hX : X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op =
        X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          X.toGenRelFunctor.map u.op := by
      rw [op_comp, Functor.map_comp]
    have hM : (mapObj F X).toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op =
        (mapObj F X).toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          (mapObj F X).toGenRelFunctor.map u.op := by
      rw [op_comp, Functor.map_comp]
    rw [hM, hX, F.map_comp, toGenRelFunctor_mapObj_map_σ_op, ih]
    rfl

/-- GenRel-op comparison for postcomposition at an arbitrary morphism. -/
private theorem toGenRelFunctor_mapObj_map (F : C ⥤ D) (X : Data C)
    {A B : SimplexCategoryGenRelᵒᵖ} (f : A ⟶ B) :
    (mapObj F X).toGenRelFunctor.map f =
      F.map (X.toGenRelFunctor.map f) := by
  have h : f = f.unop.op := (Quiver.Hom.op_unop f).symm
  rw [h]
  exact toGenRelFunctor_mapObj_map_op F X f.unop

/--
Simplicial comparison for postcomposition at an arbitrary simplex map,
via the canonical inverse and `Functor.map_comp`.
-/
theorem toSimplicialObject_mapObj_map (F : C ⥤ D) (X : Data C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (mapObj F X).toSimplicialObject.map f =
      F.map (X.toSimplicialObject.map f) := by
  have hX : X.toSimplicialObject.map f =
      X.toGenRelFunctor.map (SimplexCategoryGenRel.fromSimplexCategory.op.map f) :=
    rfl
  have hM : (mapObj F X).toSimplicialObject.map f =
      (mapObj F X).toGenRelFunctor.map
        (SimplexCategoryGenRel.fromSimplexCategory.op.map f) :=
    rfl
  rw [hM, hX]
  exact toGenRelFunctor_mapObj_map F X _

/-- Object equality for postcomposition comparison. -/
private theorem toSimplicialObject_mapObj_obj (F : C ⥤ D) (X : Data C)
    (Δ : SimplexCategoryᵒᵖ) :
    (X.toSimplicialObject ⋙ F).obj Δ = (mapObj F X).toSimplicialObject.obj Δ := by
  simp only [Functor.comp_obj, toSimplicialObject_obj, mapObj_obj]

/--
Postcomposition comparison for the data-to-simplicial transport.

Orientation `(X.toSimplicialObject ⋙ F) ≅ (mapObj F X).toSimplicialObject`.
Both components are identity isomorphisms (`eqToHom` of the object equality);
arbitrary-map naturality is the propositional commutation
`toSimplicialObject_mapObj_map`, proved by GenRel generator induction with
`Functor.map_comp` / `map_id`, not by definitional equality.
-/
noncomputable def toSimplicialObject_mapObjIso (F : C ⥤ D) (X : Data C) :
    (X.toSimplicialObject ⋙ F) ≅ (mapObj F X).toSimplicialObject where
  hom :=
    { app := fun Δ => eqToHom (by simp only [Functor.comp_obj, toSimplicialObject_obj, mapObj_obj])
      naturality := fun Δ Δ' f => by
        have h_map := toSimplicialObject_mapObj_map F X f
        rw [h_map]
        cases toSimplicialObject_mapObj_obj F X Δ
        cases toSimplicialObject_mapObj_obj F X Δ'
        change F.map (X.toSimplicialObject.map f) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (X.toSimplicialObject.map f)
        simp }
  inv :=
    { app := fun Δ =>
        eqToHom ((show (X.toSimplicialObject ⋙ F).obj Δ =
          (mapObj F X).toSimplicialObject.obj Δ from by
          simp only [Functor.comp_obj, toSimplicialObject_obj, mapObj_obj]).symm)
      naturality := fun Δ Δ' f => by
        have h_map := toSimplicialObject_mapObj_map F X f
        rw [h_map]
        cases toSimplicialObject_mapObj_obj F X Δ
        cases toSimplicialObject_mapObj_obj F X Δ'
        change F.map (X.toSimplicialObject.map f) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (X.toSimplicialObject.map f)
        simp }
  hom_inv_id := by
    ext Δ
    cases toSimplicialObject_mapObj_obj F X Δ
    simp
  inv_hom_id := by
    ext Δ
    cases toSimplicialObject_mapObj_obj F X Δ
    simp

/-- Hom component of the postcomposition comparison is the identity at `mk n`. -/
@[simp]
theorem toSimplicialObject_mapObjIso_hom_app_mk (F : C ⥤ D) (X : Data C) (n : ℕ) :
    (toSimplicialObject_mapObjIso F X).hom.app (op (SimplexCategory.mk n)) = 𝟙 _ := by
  cases toSimplicialObject_mapObj_obj F X (op (SimplexCategory.mk n))
  rfl

@[simp]
theorem toSimplicialObject_mapObjIso_inv_app_mk (F : C ⥤ D) (X : Data C) (n : ℕ) :
    (toSimplicialObject_mapObjIso F X).inv.app (op (SimplexCategory.mk n)) = 𝟙 _ := by
  cases toSimplicialObject_mapObj_obj F X (op (SimplexCategory.mk n))
  rfl

/--
Functor-level postcomposition comparison for the data-to-simplicial transport.

Orientation `(toSimplicialFunctor ⋙ whiskering.obj F) ≅ (mapFunctor F ⋙ toSimplicialFunctor)`,
consistent with the objectwise `toSimplicialObject_mapObjIso`. Object components reuse
`toSimplicialObject_mapObjIso`; naturality in `X` follows from the established
`toSimplicialFunctor_map_app` / `mapFunctor_map_app` computation.
-/
noncomputable def toSimplicialFunctor_mapFunctorIso (F : C ⥤ D) :
    (toSimplicialFunctor (C := C) ⋙ (SimplicialObject.whiskering C D).obj F) ≅
    (mapFunctor F ⋙ toSimplicialFunctor (C := D)) :=
  NatIso.ofComponents
    (fun X => toSimplicialObject_mapObjIso F X)
    (fun {X Y} f => by
      ext Δ
      have hL : (((toSimplicialFunctor (C := C) ⋙
        (SimplicialObject.whiskering C D).obj F).map f).app Δ) =
          F.map (f.app (unop Δ).len) := by
        have hcomp : (((toSimplicialFunctor (C := C) ⋙
          (SimplicialObject.whiskering C D).obj F).map f).app Δ) =
            ((((SimplicialObject.whiskering C D).obj F).map
              ((toSimplicialFunctor (C := C)).map f)).app Δ) := by
          simp only [Functor.comp_map]
        rw [hcomp, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
          toSimplicialFunctor_map_app]
        rfl
      have hR : (((mapFunctor F ⋙ toSimplicialFunctor (C := D)).map f).app Δ) =
          F.map (f.app (unop Δ).len) := by
        have h1 : (((mapFunctor F ⋙ toSimplicialFunctor (C := D)).map f).app Δ) =
          ((mapFunctor F).map f).app (unop Δ).len := by
          have hcomp : (((mapFunctor F ⋙ toSimplicialFunctor (C := D)).map f).app Δ) =
            ((toSimplicialFunctor (C := D)).map ((mapFunctor F).map f)).app Δ := by
            simp only [Functor.comp_map]
          rw [hcomp, toSimplicialFunctor_map_app]
        rw [h1, mapFunctor_map_app]
      simp only [NatTrans.comp_app, hL, hR]
      cases toSimplicialObject_mapObj_obj F X Δ
      cases toSimplicialObject_mapObj_obj F Y Δ
      change F.map (f.app (unop Δ).len) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.app (unop Δ).len)
      simp)

@[simp]
theorem toSimplicialFunctor_mapFunctorIso_hom_app_app_mk (F : C ⥤ D) (X : Data C)
    (n : ℕ) :
    ((toSimplicialFunctor_mapFunctorIso F).hom.app X).app
      (op (SimplexCategory.mk n)) = 𝟙 _ := by
  change (toSimplicialObject_mapObjIso F X).hom.app _ = _
  simp

@[simp]
theorem toSimplicialFunctor_mapFunctorIso_inv_app_app_mk (F : C ⥤ D) (X : Data C)
    (n : ℕ) :
    ((toSimplicialFunctor_mapFunctorIso F).inv.app X).app
      (op (SimplexCategory.mk n)) = 𝟙 _ := by
  change (toSimplicialObject_mapObjIso F X).inv.app _ = _
  simp

end Data

end SimplicialObject

end CategoryTheory
