/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataAugmented
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRev

/-!
# Augmented data reversal

Degreewise reversal of augmented simplicial data: `rev` applies `Data.rev`
to the left component while the augmentation point and the degreewise
augmentation components are unchanged (naturality uses `Fin.rev` indices).
This is the data-level reversal used before genuine transport; double
reversal is not claimed definitionally.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.SimplicialObject.Data.Augmented

variable {C : Type u} [Category.{v} C]

/--
Degreewise reversal on augmented simplicial data: left side is `Data.rev`,
the right point is unchanged, and the augmentation keeps the same degreewise
components as `X.hom`. The reversed augmentation uses `w_δ i.rev` and
`w_σ i.rev`.
-/
def rev (X : Augmented C) : Augmented C where
  left := Data.rev X.left
  right := X.right
  hom :=
    { app := fun n => X.hom.app n
      w_δ := fun {n} i => X.hom.w_δ (n := n) i.rev
      w_σ := fun {n} i => X.hom.w_σ (n := n) i.rev
    }

@[simp]
theorem rev_left (X : Augmented C) : (rev X).left = Data.rev X.left :=
  rfl

@[simp]
theorem rev_right (X : Augmented C) : (rev X).right = X.right :=
  rfl

@[simp]
theorem rev_hom (X : Augmented C) :
    (rev X).hom =
      { app := fun n => X.hom.app n
        w_δ := fun {n} i => X.hom.w_δ (n := n) i.rev
        w_σ := fun {n} i => X.hom.w_σ (n := n) i.rev
      } :=
  rfl

@[simp]
theorem rev_hom_app (X : Augmented C) (n : ℕ) : (rev X).hom.app n = X.hom.app n :=
  rfl

@[simp]
theorem rev_left_obj (X : Augmented C) (n : ℕ) :
    (rev X).left.obj n = X.left.obj n :=
  rfl

theorem rev_left_δ (X : Augmented C) (n : ℕ) (i : Fin (n + 2)) :
    (rev X).left.δ i = X.left.δ i.rev :=
  rfl

theorem rev_left_σ (X : Augmented C) (n : ℕ) (i : Fin (n + 1)) :
    (rev X).left.σ i = X.left.σ i.rev :=
  rfl

@[simp]
theorem rev_obj_left_δ (X : Augmented C) {n : ℕ} (i : Fin (n + 2)) :
    (rev X).left.δ (n := n) i = X.left.δ (n := n) i.rev :=
  rfl

@[simp]
theorem rev_obj_left_σ (X : Augmented C) {n : ℕ} (i : Fin (n + 1)) :
    (rev X).left.σ (n := n) i = X.left.σ (n := n) i.rev :=
  rfl

/--
Morphism of augmented data after reversal: left component is `Data.revHom`,
right component is unchanged.
-/
def revHom {X Y : Augmented C} (f : X ⟶ Y) : rev X ⟶ rev Y where
  left := Data.revHom f.left
  right := f.right
  w := by
    apply Data.Hom.ext
    intro n
    have h := f.w
    have h_app : (f.left ≫ Y.hom).app n =
        (X.hom ≫ constDataHom f.right).app n :=
      congrArg (fun g : Data.Hom _ _ => g.app n) h
    have h1 : (Data.revHom f.left ≫ (rev Y).hom).app n =
        (f.left ≫ Y.hom).app n := rfl
    have h3 : (X.hom ≫ constDataHom f.right).app n =
        ((rev X).hom ≫ constDataHom f.right).app n := rfl
    exact h1.trans (h_app.trans h3.symm)

@[simp]
theorem revHom_left {X Y : Augmented C} (f : X ⟶ Y) :
    (revHom f).left = Data.revHom f.left :=
  rfl

@[simp]
theorem revHom_right {X Y : Augmented C} (f : X ⟶ Y) :
    (revHom f).right = f.right :=
  rfl

@[simp]
theorem revHom_left_app {X Y : Augmented C} (f : X ⟶ Y) (n : ℕ) :
    (revHom f).left.app n = f.left.app n :=
  rfl

/-- Functor `Augmented C ⥤ Augmented C` induced by degreewise reversal. -/
def revFunctor : Augmented C ⥤ Augmented C where
  obj X := rev X
  map f := revHom f
  map_id X := by
    apply CommaMorphism.ext
    · exact Data.revHom_id X.left
    · rfl
  map_comp f g := by
    apply CommaMorphism.ext
    · exact Data.revHom_comp f.left g.left
    · rfl

@[simp]
theorem revFunctor_obj (X : Augmented C) : (revFunctor (C := C)).obj X = rev X :=
  rfl

@[simp]
theorem revFunctor_obj_left (X : Augmented C) :
    ((revFunctor (C := C)).obj X).left = Data.rev X.left :=
  rfl

@[simp]
theorem revFunctor_obj_right (X : Augmented C) :
    ((revFunctor (C := C)).obj X).right = X.right :=
  rfl

@[simp]
theorem revFunctor_obj_hom_app (X : Augmented C) (n : ℕ) :
    ((revFunctor (C := C)).obj X).hom.app n = X.hom.app n :=
  rfl

@[simp]
theorem revFunctor_map (X Y : Augmented C) (f : X ⟶ Y) :
    (revFunctor (C := C)).map f = revHom f :=
  rfl

@[simp]
theorem revFunctor_map_left (X Y : Augmented C) (f : X ⟶ Y) :
    ((revFunctor (C := C)).map f).left = Data.revHom f.left :=
  rfl

@[simp]
theorem revFunctor_map_right (X Y : Augmented C) (f : X ⟶ Y) :
    ((revFunctor (C := C)).map f).right = f.right :=
  rfl

@[simp]
theorem revFunctor_map_left_app (X Y : Augmented C) (f : X ⟶ Y) (n : ℕ) :
    ((revFunctor (C := C)).map f).left.app n = f.left.app n :=
  rfl

def revCompRevIsoAux (X : Augmented C) : (revFunctor ⋙ revFunctor).obj X ≅ X where
  hom :=
    { left := Data.revCompRevIso.hom.app X.left
      right := 𝟙 X.right
      w := by
        apply Data.Hom.ext
        intro n
        have hY : ((revFunctor ⋙ revFunctor).obj X).hom.app n = X.hom.app n := rfl
        have hL : (Data.revCompRevIso.hom.app X.left ≫ X.hom).app n = X.hom.app n := by
          have : (Data.revCompRevIso.hom.app X.left ≫ X.hom).app n =
              (Data.revCompRevIso.hom.app X.left).app n ≫ X.hom.app n := rfl
          rw [this, Data.revCompRevIso_hom_app_app]
          exact Category.id_comp _
        have hR : (((revFunctor ⋙ revFunctor).obj X).hom ≫
            constFunctor.map (𝟙 X.right)).app n = X.hom.app n := by
          have hcomp : (((revFunctor ⋙ revFunctor).obj X).hom ≫
              constFunctor.map (𝟙 X.right)).app n =
              (((revFunctor ⋙ revFunctor).obj X).hom.app n ≫
                (constFunctor.map (𝟙 X.right)).app n) := rfl
          have hmap : (constFunctor.map (𝟙 X.right)).app n = 𝟙 X.right :=
            Data.constFunctor_map_app _ _ _ _
          rw [hcomp, hmap]
          exact (Category.comp_id _).trans hY
        exact hL.trans hR.symm
    }
  inv :=
    { left := Data.revCompRevIso.inv.app X.left
      right := 𝟙 X.right
      w := by
        apply Data.Hom.ext
        intro n
        have hY : ((revFunctor ⋙ revFunctor).obj X).hom.app n = X.hom.app n := rfl
        have hL : (Data.revCompRevIso.inv.app X.left ≫
            ((revFunctor ⋙ revFunctor).obj X).hom).app n = X.hom.app n := by
          have : (Data.revCompRevIso.inv.app X.left ≫
              ((revFunctor ⋙ revFunctor).obj X).hom).app n =
              (Data.revCompRevIso.inv.app X.left).app n ≫
                ((revFunctor ⋙ revFunctor).obj X).hom.app n := rfl
          rw [this, Data.revCompRevIso_inv_app_app, hY]
          exact Category.id_comp _
        have hR : (X.hom ≫ constFunctor.map (𝟙 X.right)).app n = X.hom.app n := by
          have hcomp : (X.hom ≫ constFunctor.map (𝟙 X.right)).app n =
              (X.hom.app n ≫ (constFunctor.map (𝟙 X.right)).app n) := rfl
          have hmap : (constFunctor.map (𝟙 X.right)).app n = 𝟙 X.right :=
            Data.constFunctor_map_app _ _ _ _
          rw [hcomp, hmap]
          exact Category.comp_id _
        exact hL.trans hR.symm
    }
  hom_inv_id := by
    apply CommaMorphism.ext
    · exact (Data.revCompRevIso.app X.left).hom_inv_id
    · exact Category.comp_id _
  inv_hom_id := by
    apply CommaMorphism.ext
    · exact (Data.revCompRevIso.app X.left).inv_hom_id
    · exact Category.comp_id _

/--
Involutivity of augmented reversal: `revFunctor ⋙ revFunctor ≅ 𝟭`.
Left component is the `Data.revCompRevIso`, right component is identity,
comma compatibility follows from the degreewise `𝟙` formulas.
-/
def revCompRevIso : revFunctor ⋙ revFunctor ≅ 𝟭 (Augmented C) :=
  NatIso.ofComponents
    (fun X => revCompRevIsoAux X)
    (by
      intro X Y f
      apply CommaMorphism.ext
      · have hLHS : ((revFunctor ⋙ revFunctor).map f ≫ (revCompRevIsoAux Y).hom).left =
            (Data.revFunctor ⋙ Data.revFunctor).map f.left ≫
              Data.revCompRevIso.hom.app Y.left := rfl
        have hRHS : ((revCompRevIsoAux X).hom ≫ (𝟭 (Augmented C)).map f).left =
            Data.revCompRevIso.hom.app X.left ≫ f.left := rfl
        rw [hLHS, hRHS]
        exact Data.revCompRevIso.hom.naturality f.left
      · have hLHS : ((revFunctor ⋙ revFunctor).map f ≫ (revCompRevIsoAux Y).hom).right =
            f.right ≫ 𝟙 Y.right := rfl
        have hRHS : ((revCompRevIsoAux X).hom ≫ (𝟭 (Augmented C)).map f).right =
            𝟙 X.right ≫ f.right := rfl
        rw [hLHS, hRHS, Category.comp_id, Category.id_comp]
    )

@[simp]
theorem revCompRevIso_hom_left (X : Augmented C) :
    (revCompRevIso.hom.app X).left = Data.revCompRevIso.hom.app X.left :=
  rfl

@[simp]
theorem revCompRevIso_hom_right (X : Augmented C) :
    (revCompRevIso.hom.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIso_inv_left (X : Augmented C) :
    (revCompRevIso.inv.app X).left = Data.revCompRevIso.inv.app X.left :=
  rfl

@[simp]
theorem revCompRevIso_inv_right (X : Augmented C) :
    (revCompRevIso.inv.app X).right = 𝟙 X.right :=
  rfl

@[simp]
theorem revCompRevIso_hom_left_app (X : Augmented C) (n : ℕ) :
    (revCompRevIso.hom.app X).left.app n = 𝟙 _ :=
  rfl

@[simp]
theorem revCompRevIso_inv_left_app (X : Augmented C) (n : ℕ) :
    (revCompRevIso.inv.app X).left.app n = 𝟙 _ :=
  rfl

def revEquivalence : Augmented C ≌ Augmented C where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
  functor_unitIso_comp X := by
    apply CommaMorphism.ext
    · apply Data.Hom.ext
      intro n
      have h_comp : (revFunctor.map (revCompRevIso.symm.hom.app X) ≫
          revCompRevIso.hom.app (revFunctor.obj X)).left.app n =
          (revFunctor.map (revCompRevIso.symm.hom.app X)).left.app n ≫
          (revCompRevIso.hom.app (revFunctor.obj X)).left.app n := rfl
      rw [h_comp, revFunctor_map_left_app, Iso.symm_hom,
        revCompRevIso_hom_left_app, revCompRevIso_inv_left_app]
      exact Category.comp_id _
    · have h_comp : (revFunctor.map (revCompRevIso.symm.hom.app X) ≫
          revCompRevIso.hom.app (revFunctor.obj X)).right =
          (revFunctor.map (revCompRevIso.symm.hom.app X)).right ≫
          (revCompRevIso.hom.app (revFunctor.obj X)).right := rfl
      rw [h_comp, revFunctor_map_right, Iso.symm_hom, revCompRevIso_hom_right,
        revCompRevIso_inv_right]
      exact Category.comp_id _

end Augmented

end Data
end SimplicialObject
end CategoryTheory

end
