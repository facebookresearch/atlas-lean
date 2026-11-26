/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData

/-! # Degreewise isomorphisms of simplicial data

Morphisms and isomorphisms of `Data` assembled from compatible degreewise
isomorphisms `X.obj n ≅ Y.obj n`. The forward family gives `X ⟶ Y`,
with the inverse family giving the reverse direction. -/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

namespace SimplicialObject

namespace Data

variable {C : Type u} [Category.{v} C] {X Y : Data C}

section OfIso

variable {X Y : Data C}

/-- Forward morphism `X ⟶ Y` of simplicial data from a compatible degreewise family. -/
def isoHom {X Y : Data C} (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom) :
    Hom X Y where
  app n := (e n).hom
  w_δ := hδ
  w_σ := hσ

@[simp]
theorem isoHom_app {X Y : Data C} (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom)
    (n : ℕ) :
    (isoHom e hδ hσ).app n = (e n).hom :=
  rfl

private theorem inv_w_δ_aux {X Y : Data C}
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    {n : ℕ} (i : Fin (n + 2)) :
    Y.δ i ≫ (e n).inv = (e (n + 1)).inv ≫ X.δ i := by
  calc
    Y.δ i ≫ (e n).inv
        = ((e (n + 1)).inv ≫ (e (n + 1)).hom) ≫ Y.δ i ≫ (e n).inv := by
          rw [(e (n + 1)).inv_hom_id]
          simp
    _ = (e (n + 1)).inv ≫ ((e (n + 1)).hom ≫ Y.δ i) ≫ (e n).inv := by
          simp [Category.assoc]
    _ = (e (n + 1)).inv ≫ (X.δ i ≫ (e n).hom) ≫ (e n).inv := by
          rw [hδ i]
    _ = (e (n + 1)).inv ≫ X.δ i ≫ ((e n).hom ≫ (e n).inv) := by
          simp [Category.assoc]
    _ = (e (n + 1)).inv ≫ X.δ i := by
          rw [(e n).hom_inv_id]
          simp

private theorem inv_w_σ_aux {X Y : Data C}
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (_hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom)
    {n : ℕ} (i : Fin (n + 1)) :
    (e n).inv ≫ X.σ i = Y.σ i ≫ (e (n + 1)).inv := by
  have h : Y.σ i ≫ (e (n + 1)).inv = (e n).inv ≫ X.σ i := by
    calc
      Y.σ i ≫ (e (n + 1)).inv
          = ((e n).inv ≫ (e n).hom) ≫ Y.σ i ≫ (e (n + 1)).inv := by
            rw [(e n).inv_hom_id]
            simp
      _ = (e n).inv ≫ ((e n).hom ≫ Y.σ i) ≫ (e (n + 1)).inv := by
            simp [Category.assoc]
      _ = (e n).inv ≫ (X.σ i ≫ (e (n + 1)).hom) ≫ (e (n + 1)).inv := by
            rw [hσ i]
      _ = (e n).inv ≫ X.σ i ≫ ((e (n + 1)).hom ≫ (e (n + 1)).inv) := by
            simp [Category.assoc]
      _ = (e n).inv ≫ X.σ i := by
            rw [(e (n + 1)).hom_inv_id]
            simp
  exact h.symm

def isoInvHom {X Y : Data C} (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom) :
    Hom Y X where
  app n := (e n).inv
  w_δ := by
    intro n i
    exact (inv_w_δ_aux e hδ i).symm
  w_σ := by
    intro n i
    exact inv_w_σ_aux e hδ hσ i

@[simp]
theorem isoInvHom_app {X Y : Data C} (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom)
    (n : ℕ) :
    (isoInvHom e hδ hσ).app n = (e n).inv :=
  rfl

end OfIso

section Iso

variable {X Y : Data C}

/-- Isomorphism `X ≅ Y` of simplicial data from a compatible degreewise forward family. -/
noncomputable def isoOfIso (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom) :
    X ≅ Y where
  hom := isoHom e hδ hσ
  inv := isoInvHom e hδ hσ
  hom_inv_id := by
    apply Hom.ext
    intro n
    simp
  inv_hom_id := by
    apply Hom.ext
    intro n
    simp

@[simp]
theorem isoOfIso_hom_app
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom)
    (n : ℕ) :
    (isoOfIso e hδ hσ).hom.app n = (e n).hom :=
  rfl

@[simp]
theorem isoOfIso_inv_app
    (e : ∀ n, X.obj n ≅ Y.obj n)
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), (e (n + 1)).hom ≫ Y.δ i = X.δ i ≫ (e n).hom)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), (e n).hom ≫ Y.σ i = X.σ i ≫ (e (n + 1)).hom)
    (n : ℕ) :
    (isoOfIso e hδ hσ).inv.app n = (e n).inv :=
  rfl

end Iso

section HomIso

variable {X Y : Data C}

/-- Upgrade a morphism `X ⟶ Y` with degreewise isomorphisms to `X ≅ Y`. -/
noncomputable def isoOfHom (f : X ⟶ Y) (hf : ∀ n, IsIso (f.app n)) : X ≅ Y where
  hom := f
  inv :=
    { app n := inv (f.app n)
      w_δ := by
        intro n i
        have hfi : f.app (n + 1) ≫ Y.δ i = X.δ i ≫ f.app n := f.w_δ i
        have : IsIso (f.app n) := hf n
        have : IsIso (f.app (n + 1)) := hf (n + 1)
        calc
          inv (f.app (n + 1)) ≫ X.δ i
              = inv (f.app (n + 1)) ≫ X.δ i ≫ 𝟙 _ := by simp
          _ = inv (f.app (n + 1)) ≫ X.δ i ≫ (f.app n ≫ inv (f.app n)) := by
                rw [IsIso.hom_inv_id]
          _ = inv (f.app (n + 1)) ≫ (X.δ i ≫ f.app n) ≫ inv (f.app n) := by
                simp [Category.assoc]
          _ = inv (f.app (n + 1)) ≫ (f.app (n + 1) ≫ Y.δ i) ≫ inv (f.app n) := by
                rw [← hfi]
          _ = (inv (f.app (n + 1)) ≫ f.app (n + 1)) ≫ Y.δ i ≫ inv (f.app n) := by
                simp [Category.assoc]
          _ = Y.δ i ≫ inv (f.app n) := by
                rw [IsIso.inv_hom_id]
                simp
      w_σ := by
        intro n i
        have hfi : f.app n ≫ Y.σ i = X.σ i ≫ f.app (n + 1) := f.w_σ i
        have : IsIso (f.app n) := hf n
        have : IsIso (f.app (n + 1)) := hf (n + 1)
        calc
          inv (f.app n) ≫ X.σ i
              = inv (f.app n) ≫ X.σ i ≫ 𝟙 _ := by simp
          _ = inv (f.app n) ≫ X.σ i ≫ (f.app (n + 1) ≫ inv (f.app (n + 1))) := by
                rw [IsIso.hom_inv_id]
          _ = inv (f.app n) ≫ (X.σ i ≫ f.app (n + 1)) ≫ inv (f.app (n + 1)) := by
                simp [Category.assoc]
          _ = inv (f.app n) ≫ (f.app n ≫ Y.σ i) ≫ inv (f.app (n + 1)) := by
                rw [← hfi]
          _ = (inv (f.app n) ≫ f.app n) ≫ Y.σ i ≫ inv (f.app (n + 1)) := by
                simp [Category.assoc]
          _ = Y.σ i ≫ inv (f.app (n + 1)) := by
                rw [IsIso.inv_hom_id]
                simp }
  hom_inv_id := by
    apply Hom.ext
    intro n
    have : IsIso (f.app n) := hf n
    simp
  inv_hom_id := by
    apply Hom.ext
    intro n
    have : IsIso (f.app n) := hf n
    simp

theorem isIso_of_isIso (f : X ⟶ Y) (hf : ∀ n, IsIso (f.app n)) : IsIso f where
  out := ⟨(isoOfHom f hf).inv, (isoOfHom f hf).hom_inv_id, (isoOfHom f hf).inv_hom_id⟩

/--
A morphism of simplicial data is an isomorphism when all of its degreewise components are
isomorphisms.
-/
instance (priority := 100) isIso_of_isIso_app (f : X ⟶ Y) [∀ n, IsIso (f.app n)] : IsIso f :=
  isIso_of_isIso f (fun _ ↦ inferInstance)

end HomIso

end Data

end SimplicialObject

end CategoryTheory
