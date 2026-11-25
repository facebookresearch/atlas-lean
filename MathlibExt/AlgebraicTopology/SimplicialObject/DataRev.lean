/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData
public import Mathlib.Data.Fin.Rev

/-!
# Simplex reversal for simplicial data

Degreewise reversal of `Data`: objects are unchanged while faces and degeneracies
are reindexed by `Fin.rev`. Reversal exchanges left- and right-handed simplicial
structure, so it transports handed constructions (augmentations, extra degeneracies)
to the opposite side without changing the underlying degrees.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Data

variable {C : Type u} [Category.{v} C]

/--
Covariant degreewise reversal of simplicial data: objects are unchanged, faces and
degeneracies use reversed `Fin` indices.
-/
def rev (X : Data C) : Data C where
  obj n := X.obj n
  δ i := X.δ i.rev
  σ i := X.σ i.rev
  δ_comp_δ := by
    intro n i j h
    have h_rev : j.rev ≤ i.rev := by
      rw [Fin.rev_le_rev]
      exact h
    have h_eq := X.δ_comp_δ h_rev
    calc
      X.δ (j.succ).rev ≫ X.δ i.rev
          = X.δ (j.rev.castSucc) ≫ X.δ i.rev := by rw [Fin.rev_succ]
      _ = X.δ (i.rev.succ) ≫ X.δ j.rev := h_eq.symm
      _ = X.δ (i.castSucc).rev ≫ X.δ j.rev := by rw [Fin.rev_castSucc]
  δ_comp_σ_of_le := by
    intro n i j h
    have h_rev_cast_le : (j.castSucc).rev ≤ i.rev := by
      rw [Fin.rev_le_rev]
      exact h
    have h_succ_le : (j.rev).succ ≤ i.rev := by
      rw [Fin.rev_castSucc] at h_rev_cast_le
      exact h_rev_cast_le
    have h_rev_lt : (j.rev).castSucc < i.rev :=
      lt_of_lt_of_le (Fin.castSucc_lt_succ (i := j.rev)) h_succ_le
    have h_eq := X.δ_comp_σ_of_gt h_rev_lt
    calc
      X.σ (j.succ).rev ≫ X.δ (i.castSucc).rev
          = X.σ (j.rev.castSucc) ≫ X.δ (i.rev.succ) := by
            rw [Fin.rev_succ, Fin.rev_castSucc]
      _ = X.δ i.rev ≫ X.σ j.rev := h_eq
  δ_comp_σ_self := by
    intro n i
    calc
      X.σ i.rev ≫ X.δ (i.castSucc).rev
          = X.σ i.rev ≫ X.δ (i.rev.succ) := by rw [Fin.rev_castSucc]
      _ = 𝟙 _ := X.δ_comp_σ_succ
  δ_comp_σ_succ := by
    intro n i
    calc
      X.σ i.rev ≫ X.δ (i.succ).rev
          = X.σ i.rev ≫ X.δ (i.rev.castSucc) := by rw [Fin.rev_succ]
      _ = 𝟙 _ := X.δ_comp_σ_self
  δ_comp_σ_of_gt := by
    intro n i j h
    have h_rev_strict : i.rev < (j.castSucc).rev := by
      rw [Fin.rev_lt_rev]
      exact h
    have h_rev_strict' : i.rev < (j.rev).succ := by
      rw [Fin.rev_castSucc] at h_rev_strict
      exact h_rev_strict
    have h_rev_le : i.rev ≤ (j.rev).castSucc := by
      rw [Fin.le_castSucc_iff]
      exact h_rev_strict'
    have h_eq := X.δ_comp_σ_of_le h_rev_le
    calc
      X.σ (j.castSucc).rev ≫ X.δ (i.succ).rev
          = X.σ (j.rev.succ) ≫ X.δ (i.rev.castSucc) := by
            rw [Fin.rev_castSucc, Fin.rev_succ]
      _ = X.δ i.rev ≫ X.σ j.rev := h_eq
  σ_comp_σ := by
    intro n i j h
    have h_rev : j.rev ≤ i.rev := by
      rw [Fin.rev_le_rev]
      exact h
    have h_eq := X.σ_comp_σ h_rev
    calc
      X.σ j.rev ≫ X.σ (i.castSucc).rev
          = X.σ j.rev ≫ X.σ (i.rev.succ) := by rw [Fin.rev_castSucc]
      _ = X.σ i.rev ≫ X.σ (j.rev.castSucc) := h_eq.symm
      _ = X.σ i.rev ≫ X.σ (j.succ).rev := by rw [Fin.rev_succ]

@[simp]
theorem rev_obj (X : Data C) (n : ℕ) : (rev X).obj n = X.obj n :=
  rfl

@[simp]
theorem rev_δ (X : Data C) {n : ℕ} (i : Fin (n + 2)) : (rev X).δ i = X.δ i.rev :=
  rfl

@[simp]
theorem rev_σ (X : Data C) {n : ℕ} (i : Fin (n + 1)) : (rev X).σ i = X.σ i.rev :=
  rfl

/-- A data morphism keeps the same degreewise components after reversal. -/
def revHom {X Y : Data C} (f : X ⟶ Y) : rev X ⟶ rev Y where
  app n := f.app n
  w_δ i := f.w_δ i.rev
  w_σ i := f.w_σ i.rev

@[simp]
theorem revHom_app {X Y : Data C} (f : X ⟶ Y) (n : ℕ) : (revHom f).app n = f.app n :=
  rfl

theorem revHom_id (X : Data C) : revHom (𝟙 X) = 𝟙 (rev X) := by
  apply Hom.ext
  intro n
  rfl

theorem revHom_comp {X Y Z : Data C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    revHom (f ≫ g) = revHom f ≫ revHom g := by
  apply Hom.ext
  intro n
  rfl

/-- Functor `Data C ⥤ Data C` induced by degreewise reversal. -/
def revFunctor : Data C ⥤ Data C where
  obj X := rev X
  map f := revHom f
  map_id X := by
    apply Hom.ext
    intro n
    rfl
  map_comp f g := by
    apply Hom.ext
    intro n
    rfl

@[simp]
theorem revFunctor_obj (X : Data C) : (revFunctor (C := C)).obj X = rev X :=
  rfl

@[simp]
theorem revFunctor_map {X Y : Data C} (f : X ⟶ Y) :
    (revFunctor (C := C)).map f = revHom f :=
  rfl

@[simp]
theorem revFunctor_obj_obj (X : Data C) (n : ℕ) :
    ((revFunctor (C := C)).obj X).obj n = X.obj n :=
  rfl

@[simp]
theorem revFunctor_obj_δ (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    ((revFunctor (C := C)).obj X).δ i = X.δ i.rev :=
  rfl

@[simp]
theorem revFunctor_obj_σ (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    ((revFunctor (C := C)).obj X).σ i = X.σ i.rev :=
  rfl

@[simp]
theorem revFunctor_map_app {X Y : Data C} (f : X ⟶ Y) (n : ℕ) :
    ((revFunctor (C := C)).map f).app n = f.app n :=
  rfl

/--
Double-reversal isomorphism `revFunctor ⋙ revFunctor ≅ 𝟭 (Data C)`.
Both components are identities degreewise, so double reversal is the identity
propositionally but not definitionally: `Fin.rev` is involutive only up to
`Fin.rev_rev`.
-/
def revCompRevIso : revFunctor ⋙ revFunctor ≅ 𝟭 (Data C) :=
  NatIso.ofComponents
    (fun X =>
      { hom :=
          { app := fun _ => 𝟙 _
            w_δ := by
              intro n i
              have h : i.rev.rev = i := Fin.rev_rev i
              dsimp
              rw [Category.id_comp, Category.comp_id]
              exact congrArg (X.δ (n := n)) h.symm
            w_σ := by
              intro n i
              have h : i.rev.rev = i := Fin.rev_rev i
              dsimp
              rw [Category.id_comp, Category.comp_id]
              exact congrArg (X.σ (n := n)) h.symm }
        inv :=
          { app := fun _ => 𝟙 _
            w_δ := by
              intro n i
              have h : i.rev.rev = i := Fin.rev_rev i
              dsimp
              rw [Category.id_comp, Category.comp_id]
              exact congrArg (X.δ (n := n)) h
            w_σ := by
              intro n i
              have h : i.rev.rev = i := Fin.rev_rev i
              dsimp
              rw [Category.id_comp, Category.comp_id]
              exact congrArg (X.σ (n := n)) h }
        hom_inv_id := by
          apply Hom.ext
          intro n
          simp only [comp_app, id_app]
          exact Category.id_comp _
        inv_hom_id := by
          apply Hom.ext
          intro n
          simp only [comp_app, id_app]
          exact Category.id_comp _ })
    (by
      intro X Y f
      apply Hom.ext
      intro n
      simp only [comp_app, Functor.comp_map, revFunctor_map_app]
      have hId : ((𝟭 (Data C)).map f).app n = f.app n := rfl
      rw [hId]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp]
theorem revCompRevIso_hom_app_app (X : Data C) (n : ℕ) :
    (revCompRevIso (C := C).hom.app X).app n = 𝟙 _ :=
  rfl

@[simp]
theorem revCompRevIso_inv_app_app (X : Data C) (n : ℕ) :
    (revCompRevIso (C := C).inv.app X).app n = 𝟙 _ :=
  rfl

@[simp]
theorem revCompRevIso_hom_app (X : Data C) :
    (revCompRevIso (C := C).hom.app X).app = fun _ => 𝟙 _ :=
  rfl

@[simp]
theorem revCompRevIso_inv_app (X : Data C) :
    (revCompRevIso (C := C).inv.app X).app = fun _ => 𝟙 _ :=
  rfl

def revEquivalence : Data C ≌ Data C where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
  functor_unitIso_comp X := by
    apply Hom.ext
    intro n
    simp only [comp_app, id_app, Iso.symm_hom, revFunctor_map_app,
      revCompRevIso_hom_app_app, revCompRevIso_inv_app_app]
    exact Category.id_comp _

end Data
end SimplicialObject
end CategoryTheory
