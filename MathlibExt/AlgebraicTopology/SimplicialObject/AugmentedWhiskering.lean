/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! Target-category postcomposition for augmented simplicial objects.

`whiskeringObj C D F : Augmented C ⥤ Augmented D` postcomposes both comma legs
with `F`: the simplicial leg through `SimplicialObject.whiskering` and the
augmentation point through `F.obj`, with augmentation map `F.map` of the
original augmentation. The lemmas below record these left/right and
degreewise comma components.

The unit comparison `whiskeringObjIdIso` (from `Functor.rightUnitor`) and the
compositor `whiskeringObjCompIso` (from `Functor.associator`) are natural
isomorphisms with identity augmentation-point components, not definitional
equalities: `F.map (𝟙 _) = 𝟙 _` and `(F ⋙ G).map = G.map ∘ F.map`, hence the
`const`-whiskering identification, hold only propositionally, so `Iso.refl`
across the compared functors is unavailable. -/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u v' u' v'' u''

namespace CategoryTheory
namespace SimplicialObject
namespace Augmented

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {E : Type u''} [Category.{v''} E]

@[simp]
theorem whiskeringObj_obj_left (F : C ⥤ D) (X : Augmented C) :
    ((whiskeringObj C D F).obj X).left =
      ((SimplicialObject.whiskering C D).obj F).obj (drop.obj X) :=
  rfl

@[simp]
theorem whiskeringObj_obj_right (F : C ⥤ D) (X : Augmented C) :
    ((whiskeringObj C D F).obj X).right = F.obj (point.obj X) :=
  rfl

@[simp]
theorem whiskeringObj_obj_drop (F : C ⥤ D) (X : Augmented C) :
    (drop.obj ((whiskeringObj C D F).obj X)) =
      ((SimplicialObject.whiskering C D).obj F).obj (drop.obj X) :=
  rfl

@[simp]
theorem whiskeringObj_obj_point (F : C ⥤ D) (X : Augmented C) :
    (point.obj ((whiskeringObj C D F).obj X)) = F.obj (point.obj X) :=
  rfl

@[simp]
theorem whiskeringObj_obj_left_obj (F : C ⥤ D) (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    ((whiskeringObj C D F).obj X).left.obj Δ = F.obj ((drop.obj X).obj Δ) :=
  rfl

@[simp]
theorem whiskeringObj_obj_left_obj_mk (F : C ⥤ D) (X : Augmented C) (n : ℕ) :
    ((whiskeringObj C D F).obj X).left.obj (op (SimplexCategory.mk n)) =
      F.obj ((drop.obj X).obj (op (SimplexCategory.mk n))) :=
  rfl

@[simp]
theorem whiskeringObj_obj_left_map_δ (F : C ⥤ D) (X : Augmented C) {n : ℕ}
    (i : Fin (n + 2)) :
    ((whiskeringObj C D F).obj X).left.map (SimplexCategory.δ i).op =
      F.map ((drop.obj X).map (SimplexCategory.δ i).op) :=
  rfl

@[simp]
theorem whiskeringObj_obj_left_map_σ (F : C ⥤ D) (X : Augmented C) {n : ℕ}
    (i : Fin (n + 1)) :
    ((whiskeringObj C D F).obj X).left.map (SimplexCategory.σ i).op =
      F.map ((drop.obj X).map (SimplexCategory.σ i).op) :=
  rfl

theorem whiskeringObj_obj_left_δ (F : C ⥤ D) (X : Augmented C) {n : ℕ}
    (i : Fin (n + 2)) :
    ((whiskeringObj C D F).obj X).left.δ i = F.map ((drop.obj X).δ i) :=
  SimplicialObject.whiskering_obj_obj_δ C F (drop.obj X) i

theorem whiskeringObj_obj_left_σ (F : C ⥤ D) (X : Augmented C) {n : ℕ}
    (i : Fin (n + 1)) :
    ((whiskeringObj C D F).obj X).left.σ i = F.map ((drop.obj X).σ i) :=
  SimplicialObject.whiskering_obj_obj_σ C F (drop.obj X) i

theorem whiskeringObj_obj_hom_app (F : C ⥤ D) (X : Augmented C)
    (Δ : SimplexCategoryᵒᵖ) :
    ((whiskeringObj C D F).obj X).hom.app Δ = F.map (X.hom.app Δ) := by
  have h : ((whiskeringObj C D F).obj X).hom.app Δ =
      F.map (X.hom.app Δ) ≫ 𝟙 _ := rfl
  rw [h]
  exact Category.comp_id _

theorem whiskeringObj_obj_hom_app_mk (F : C ⥤ D) (X : Augmented C) (n : ℕ) :
    ((whiskeringObj C D F).obj X).hom.app (op (SimplexCategory.mk n)) =
      F.map (X.hom.app (op (SimplexCategory.mk n))) := by
  have h : ((whiskeringObj C D F).obj X).hom.app (op (SimplexCategory.mk n)) =
      F.map (X.hom.app (op (SimplexCategory.mk n))) ≫ 𝟙 _ := rfl
  rw [h]
  exact Category.comp_id _

@[simp]
theorem whiskeringObj_map_left (F : C ⥤ D) {X Y : Augmented C} (f : X ⟶ Y) :
    ((whiskeringObj C D F).map f).left = Functor.whiskerRight f.left F :=
  rfl

@[simp]
theorem whiskeringObj_map_right (F : C ⥤ D) {X Y : Augmented C} (f : X ⟶ Y) :
    ((whiskeringObj C D F).map f).right = F.map f.right :=
  rfl

@[simp]
theorem whiskeringObj_map_left_app (F : C ⥤ D) {X Y : Augmented C}
    (f : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) :
    ((whiskeringObj C D F).map f).left.app Δ = F.map (f.left.app Δ) :=
  rfl

@[simp]
theorem whiskeringObj_map_left_app_mk (F : C ⥤ D) {X Y : Augmented C}
    (f : X ⟶ Y) (n : ℕ) :
    ((whiskeringObj C D F).map f).left.app (op (SimplexCategory.mk n)) =
      F.map (f.left.app (op (SimplexCategory.mk n))) :=
  rfl

/-- Object-level unit comparison for augmented whiskering.

Orientation `(whiskeringObj C C (𝟭 C)).obj X ≅ X`. Left component is the
canonical functor right unitor `Functor.rightUnitor X.left`; the
augmentation-point component is the identity iso. Isomorphism, not strict
equality; no pseudofunctor coherence is claimed here. -/
noncomputable def whiskeringObjIdIsoApp (X : Augmented C) :
    (whiskeringObj C C (𝟭 C)).obj X ≅ X :=
  Comma.isoMk
    (Functor.rightUnitor X.left)
    (Iso.refl X.right)
    (by
      ext Δ
      change (𝟙 (X.left.obj Δ)) ≫ X.hom.app Δ =
        ((whiskeringObj C C (𝟭 C)).obj X).hom.app Δ ≫ 𝟙 X.right
      rw [whiskeringObj_obj_hom_app]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Functor-level unit comparison for augmented whiskering.

Orientation `whiskeringObj C C (𝟭 C) ≅ 𝟭 (Augmented C)`. Left component is
the canonical `Functor.rightUnitor`; augmentation-point component is identity.
This is the unit comparison needed for later pseudofunctorial packaging;
isomorphism only, no coherence is claimed in this packet. -/
noncomputable def whiskeringObjIdIso :
    whiskeringObj C C (𝟭 C) ≅ 𝟭 (Augmented C) :=
  NatIso.ofComponents
    (fun X => whiskeringObjIdIsoApp X)
    (fun {X Y} f => by
      apply Augmented.hom_ext
      · ext Δ
        change f.left.app Δ ≫ 𝟙 (Y.left.obj Δ) = 𝟙 (X.left.obj Δ) ≫ f.left.app Δ
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      · change f.right ≫ 𝟙 Y.right = 𝟙 X.right ≫ f.right
        exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp]
theorem whiskeringObjIdIsoApp_hom_left (X : Augmented C) :
    (whiskeringObjIdIsoApp (C := C) X).hom.left =
      (Functor.rightUnitor X.left).hom :=
  rfl

@[simp]
theorem whiskeringObjIdIsoApp_hom_right (X : Augmented C) :
    (whiskeringObjIdIsoApp (C := C) X).hom.right = 𝟙 X.right :=
  rfl

@[simp]
theorem whiskeringObjIdIsoApp_inv_left (X : Augmented C) :
    (whiskeringObjIdIsoApp (C := C) X).inv.left =
      (Functor.rightUnitor X.left).inv :=
  rfl

@[simp]
theorem whiskeringObjIdIsoApp_inv_right (X : Augmented C) :
    (whiskeringObjIdIsoApp (C := C) X).inv.right = 𝟙 X.right :=
  rfl

@[simp]
theorem whiskeringObjIdIsoApp_hom_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjIdIsoApp (C := C) X).hom.left.app Δ = 𝟙 (X.left.obj Δ) :=
  rfl

@[simp]
theorem whiskeringObjIdIsoApp_inv_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjIdIsoApp (C := C) X).inv.left.app Δ = 𝟙 (X.left.obj Δ) :=
  rfl

@[simp]
theorem whiskeringObjIdIso_hom_app_hom_left (X : Augmented C) :
    (whiskeringObjIdIso (C := C).hom.app X).left =
      (Functor.rightUnitor X.left).hom :=
  rfl

@[simp]
theorem whiskeringObjIdIso_hom_app_hom_right (X : Augmented C) :
    (whiskeringObjIdIso (C := C).hom.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem whiskeringObjIdIso_inv_app_inv_left (X : Augmented C) :
    (whiskeringObjIdIso (C := C).inv.app X).left =
      (Functor.rightUnitor X.left).inv :=
  rfl

@[simp]
theorem whiskeringObjIdIso_inv_app_inv_right (X : Augmented C) :
    (whiskeringObjIdIso (C := C).inv.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem whiskeringObjIdIso_hom_app_hom_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjIdIso (C := C).hom.app X).left.app Δ = 𝟙 (X.left.obj Δ) :=
  rfl

@[simp]
theorem whiskeringObjIdIso_inv_app_inv_left_app (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjIdIso (C := C).inv.app X).left.app Δ = 𝟙 (X.left.obj Δ) :=
  rfl

/-- Object-level compositor comparison for augmented whiskering.

Orientation `(whiskeringObj C E (F ⋙ G)).obj X ≅
(whiskeringObj C D F ⋙ whiskeringObj D E G).obj X`. Left component is the
canonical `Functor.associator X.left F G` (symmetrized); the
augmentation-point component is the identity iso. Isomorphism, not strict
equality; no pseudofunctor coherence is claimed here. -/
noncomputable def whiskeringObjCompIsoApp (F : C ⥤ D) (G : D ⥤ E) (X : Augmented C) :
    (whiskeringObj C E (F ⋙ G)).obj X ≅
      (whiskeringObj C D F ⋙ whiskeringObj D E G).obj X :=
  Comma.isoMk
    (Functor.associator X.left F G).symm
    (Iso.refl _)
    (by
      ext Δ
      have hG : ((whiskeringObj D E G).obj ((whiskeringObj C D F).obj X)).hom.app Δ =
          G.map (((whiskeringObj C D F).obj X).hom.app Δ) :=
        whiskeringObj_obj_hom_app G ((whiskeringObj C D F).obj X) Δ
      have hF : ((whiskeringObj C D F).obj X).hom.app Δ = F.map (X.hom.app Δ) :=
        whiskeringObj_obj_hom_app F X Δ
      have hB : ((whiskeringObj D E G).obj ((whiskeringObj C D F).obj X)).hom.app Δ =
          G.map (F.map (X.hom.app Δ)) :=
        hG.trans (congrArg G.map hF)
      have hA : ((whiskeringObj C E (F ⋙ G)).obj X).hom.app Δ =
          (F ⋙ G).map (X.hom.app Δ) :=
        whiskeringObj_obj_hom_app (F ⋙ G) X Δ
      have h1 : (Functor.associator X.left F G).symm.hom.app Δ ≫
            ((whiskeringObj D E G).obj ((whiskeringObj C D F).obj X)).hom.app Δ =
          (Functor.associator X.left F G).symm.hom.app Δ ≫ G.map (F.map (X.hom.app Δ)) :=
        congrArg ((Functor.associator X.left F G).symm.hom.app Δ ≫ ·) hB
      have h2 : (Functor.associator X.left F G).symm.hom.app Δ ≫ G.map (F.map (X.hom.app Δ)) =
          𝟙 _ ≫ G.map (F.map (X.hom.app Δ)) := by rfl
      have h3 : 𝟙 _ ≫ G.map (F.map (X.hom.app Δ)) = G.map (F.map (X.hom.app Δ)) :=
        Category.id_comp _
      have h4 : G.map (F.map (X.hom.app Δ)) = (F ⋙ G).map (X.hom.app Δ) := by rfl
      have h5 : (F ⋙ G).map (X.hom.app Δ) = ((whiskeringObj C E (F ⋙ G)).obj X).hom.app Δ :=
        hA.symm
      have h6 : ((whiskeringObj C E (F ⋙ G)).obj X).hom.app Δ =
          ((whiskeringObj C E (F ⋙ G)).obj X).hom.app Δ ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))) )

/-- Functor-level compositor comparison for augmented whiskering.

Orientation `whiskeringObj C E (F ⋙ G) ≅ whiskeringObj C D F ⋙
whiskeringObj D E G`. Left component is the canonical `Functor.associator`;
augmentation-point component is identity. This is the compositor comparison
needed for later pseudofunctorial packaging; isomorphism only, no coherence
is claimed in this packet. -/
noncomputable def whiskeringObjCompIso (F : C ⥤ D) (G : D ⥤ E) :
    whiskeringObj C E (F ⋙ G) ≅
      whiskeringObj C D F ⋙ whiskeringObj D E G :=
  NatIso.ofComponents
    (fun X => whiskeringObjCompIsoApp F G X)
    (fun {X Y} f => by
      apply Augmented.hom_ext
      · ext Δ
        have h1 : (F ⋙ G).map (f.left.app Δ) ≫ (Functor.associator Y.left F G).symm.hom.app Δ =
            (F ⋙ G).map (f.left.app Δ) ≫ 𝟙 _ := by rfl
        have h2 : (F ⋙ G).map (f.left.app Δ) ≫ 𝟙 _ = (F ⋙ G).map (f.left.app Δ) :=
          Category.comp_id _
        have h3 : (F ⋙ G).map (f.left.app Δ) = G.map (F.map (f.left.app Δ)) := by rfl
        have h4 : G.map (F.map (f.left.app Δ)) = 𝟙 _ ≫ G.map (F.map (f.left.app Δ)) :=
          (Category.id_comp _).symm
        have h5 : 𝟙 _ ≫ G.map (F.map (f.left.app Δ)) =
            (Functor.associator X.left F G).symm.hom.app Δ ≫ G.map (F.map (f.left.app Δ)) := by rfl
        exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
      · have h1 : (F ⋙ G).map f.right ≫ 𝟙 _ = (F ⋙ G).map f.right := Category.comp_id _
        have h2 : (F ⋙ G).map f.right = G.map (F.map f.right) := by rfl
        have h3 : G.map (F.map f.right) = 𝟙 _ ≫ G.map (F.map f.right) :=
          (Category.id_comp _).symm
        exact h1.trans (h2.trans h3))

@[simp]
theorem whiskeringObjCompIsoApp_hom_left (F : C ⥤ D) (G : D ⥤ E) (X : Augmented C) :
    (whiskeringObjCompIsoApp F G X).hom.left =
      (Functor.associator X.left F G).symm.hom :=
  rfl

@[simp]
theorem whiskeringObjCompIsoApp_hom_right (F : C ⥤ D) (G : D ⥤ E) (X : Augmented C) :
    (whiskeringObjCompIsoApp F G X).hom.right = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIsoApp_inv_left (F : C ⥤ D) (G : D ⥤ E) (X : Augmented C) :
    (whiskeringObjCompIsoApp F G X).inv.left =
      (Functor.associator X.left F G).symm.inv :=
  rfl

@[simp]
theorem whiskeringObjCompIsoApp_inv_right (F : C ⥤ D) (G : D ⥤ E) (X : Augmented C) :
    (whiskeringObjCompIsoApp F G X).inv.right = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIsoApp_hom_left_app (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjCompIsoApp F G X).hom.left.app Δ = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIsoApp_inv_left_app (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjCompIsoApp F G X).inv.left.app Δ = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIso_hom_app_hom_left (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) :
    (whiskeringObjCompIso F G |>.hom.app X).left =
      (Functor.associator X.left F G).symm.hom :=
  rfl

@[simp]
theorem whiskeringObjCompIso_hom_app_hom_right (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) :
    (whiskeringObjCompIso F G |>.hom.app X).right = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIso_inv_app_inv_left (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) :
    (whiskeringObjCompIso F G |>.inv.app X).left =
      (Functor.associator X.left F G).symm.inv :=
  rfl

@[simp]
theorem whiskeringObjCompIso_inv_app_inv_right (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) :
    (whiskeringObjCompIso F G |>.inv.app X).right = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIso_hom_app_hom_left_app (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjCompIso F G |>.hom.app X).left.app Δ = 𝟙 _ :=
  rfl

@[simp]
theorem whiskeringObjCompIso_inv_app_inv_left_app (F : C ⥤ D) (G : D ⥤ E)
    (X : Augmented C) (Δ : SimplexCategoryᵒᵖ) :
    (whiskeringObjCompIso F G |>.inv.app X).left.app Δ = 𝟙 _ :=
  rfl

end Augmented
end SimplicialObject
end CategoryTheory
