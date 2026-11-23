/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial
public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty

/-!
# Data reversal versus genuine simplicial reversal

This module compares the two routes from `Data C` to `SimplicialObject C`:
reversing the data first and then converting (`(Data.rev X).toSimplicialObject`),
versus converting first and then applying Mathlib's genuine `opFunctor`.
The comparison `toSimplicialObjectRevIso` (packaged functorially as
`toSimplicialFunctorRevIso`) has identity morphisms as all of its degreewise
components; only naturality carries content, proved generator-wise in
`toSimplicialObject_rev_map_eq_opFunctor_map`. It is a propositional
isomorphism of functors, not a definitional equality of the two composites.
-/

@[expose] public section

open CategoryTheory Opposite SimplicialObject

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Data

variable {C : Type u} [Category.{v} C]

private def revMapEqProp (X : Data C) : MorphismProperty SimplexCategory :=
  fun {_ _} f =>
    (Data.rev X).toSimplicialObject.map f.op =
      (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f.op

private instance revMapEqProp_isMultiplicative (X : Data C) :
    (revMapEqProp X).IsMultiplicative where
  id_mem := by
    intro a
    dsimp only [revMapEqProp]
    have h1 : (Data.rev X).toSimplicialObject.map (𝟙 a).op = 𝟙 _ := by
      have : (𝟙 a).op = 𝟙 (Opposite.op a) := rfl
      rw [this]
      exact (Data.rev X).toSimplicialObject.map_id _
    have h2 : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map (𝟙 a).op = 𝟙 _ := by
      have : (𝟙 a).op = 𝟙 (Opposite.op a) := rfl
      rw [this]
      exact (SimplicialObject.opFunctor.obj X.toSimplicialObject).map_id _
    exact h1.trans h2.symm
  comp_mem := by
    intro a b c f g hf hg
    dsimp only [revMapEqProp] at *
    have h_left : (Data.rev X).toSimplicialObject.map (f ≫ g).op =
        (Data.rev X).toSimplicialObject.map g.op ≫
          (Data.rev X).toSimplicialObject.map f.op := by
      have h_op : (f ≫ g).op = g.op ≫ f.op := by
        rw [op_comp]
      calc
        (Data.rev X).toSimplicialObject.map (f ≫ g).op
            = (Data.rev X).toSimplicialObject.map (g.op ≫ f.op) := by
              rw [h_op]
        _ = (Data.rev X).toSimplicialObject.map g.op ≫
              (Data.rev X).toSimplicialObject.map f.op := by
              simp
    have h_right : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map (f ≫ g).op =
        (SimplicialObject.opFunctor.obj X.toSimplicialObject).map g.op ≫
          (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f.op := by
      have h_op : (f ≫ g).op = g.op ≫ f.op := by
        rw [op_comp]
      calc
        (SimplicialObject.opFunctor.obj X.toSimplicialObject).map (f ≫ g).op
            = (SimplicialObject.opFunctor.obj X.toSimplicialObject).map
                (g.op ≫ f.op) := by
              rw [h_op]
        _ = (SimplicialObject.opFunctor.obj X.toSimplicialObject).map g.op ≫
              (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f.op := by
              simp
    have h_mid : (Data.rev X).toSimplicialObject.map g.op ≫
        (Data.rev X).toSimplicialObject.map f.op =
        (SimplicialObject.opFunctor.obj X.toSimplicialObject).map g.op ≫
          (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f.op :=
      congrArg₂ (· ≫ ·) hg hf
    exact (h_left.trans h_mid).trans h_right.symm

private theorem revMapEqProp_δ_mem (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    revMapEqProp X (SimplexCategory.δ i) := by
  dsimp only [revMapEqProp]
  have h_left : (Data.rev X).toSimplicialObject.map (SimplexCategory.δ i).op =
      X.δ i.rev := by
    have h1 : (Data.rev X).toSimplicialObject.map (SimplexCategory.δ i).op =
        (Data.rev X).δ i :=
      toSimplicialObject_map_δ (Data.rev X) i
    have h2 : (Data.rev X).δ i = X.δ i.rev := rfl
    exact h1.trans h2
  have h_right : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map
      (SimplexCategory.δ i).op = X.δ i.rev := by
    have h1 : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map
        (SimplexCategory.δ i).op =
        X.toSimplicialObject.map (SimplexCategory.rev.map (SimplexCategory.δ i)).op := by
      rfl
    have h2 : X.toSimplicialObject.map (SimplexCategory.rev.map (SimplexCategory.δ i)).op =
        X.toSimplicialObject.map (SimplexCategory.δ i.rev).op := by
      rw [SimplexCategory.rev_map_δ]
    have h3 : X.toSimplicialObject.map (SimplexCategory.δ i.rev).op = X.δ i.rev :=
      toSimplicialObject_map_δ X i.rev
    exact (h1.trans h2).trans h3
  exact h_left.trans h_right.symm

private theorem revMapEqProp_σ_mem (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    revMapEqProp X (SimplexCategory.σ i) := by
  dsimp only [revMapEqProp]
  have h_left : (Data.rev X).toSimplicialObject.map (SimplexCategory.σ i).op =
      X.σ i.rev := by
    have h1 : (Data.rev X).toSimplicialObject.map (SimplexCategory.σ i).op =
        (Data.rev X).σ i :=
      toSimplicialObject_map_σ (Data.rev X) i
    have h2 : (Data.rev X).σ i = X.σ i.rev := rfl
    exact h1.trans h2
  have h_right : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map
      (SimplexCategory.σ i).op = X.σ i.rev := by
    have h1 : (SimplicialObject.opFunctor.obj X.toSimplicialObject).map
        (SimplexCategory.σ i).op =
        X.toSimplicialObject.map (SimplexCategory.rev.map (SimplexCategory.σ i)).op := by
      rfl
    have h2 : X.toSimplicialObject.map (SimplexCategory.rev.map (SimplexCategory.σ i)).op =
        X.toSimplicialObject.map (SimplexCategory.σ i.rev).op := by
      rw [SimplexCategory.rev_map_σ]
    have h3 : X.toSimplicialObject.map (SimplexCategory.σ i.rev).op = X.σ i.rev :=
      toSimplicialObject_map_σ X i.rev
    exact (h1.trans h2).trans h3
  exact h_left.trans h_right.symm

/-- Data reversal commutes with `toSimplicialObject` and Mathlib's `opFunctor` on arbitrary
morphisms: for any `f : a ⟶ b` in `SimplexCategory`, the two ways of reversing agree. -/
theorem toSimplicialObject_rev_map_eq_opFunctor_map (X : Data C)
    {a b : SimplexCategory} (f : a ⟶ b) :
    (Data.rev X).toSimplicialObject.map f.op =
      (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f.op := by
  have h_eq : revMapEqProp X = ⊤ := by
    apply SimplexCategory.morphismProperty_eq_top
    · intro n i
      exact revMapEqProp_δ_mem X i
    · intro n i
      exact revMapEqProp_σ_mem X i
  have h_mem : revMapEqProp X f := by
    rw [h_eq]
    trivial
  dsimp only [revMapEqProp] at h_mem
  exact h_mem

/-- Identity-component comparison between data reversal and `opFunctor`.

Every component is `𝟙 _` via `Iso.refl`; naturality is the accepted
`toSimplicialObject_rev_map_eq_opFunctor_map`. -/
noncomputable def toSimplicialObjectRevIso (X : Data C) :
    (Data.rev X).toSimplicialObject ≅
      SimplicialObject.opFunctor.obj X.toSimplicialObject :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {Δ₁ Δ₂} f => by
    change (Data.rev X).toSimplicialObject.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (SimplicialObject.opFunctor.obj X.toSimplicialObject).map f
    rw [Category.comp_id, Category.id_comp]
    have h := toSimplicialObject_rev_map_eq_opFunctor_map X f.unop
    rwa [Quiver.Hom.op_unop f] at h

/-- Deprecated compatibility name for the original reversal isomorphism. -/
@[deprecated toSimplicialObjectRevIso (since := "2026-11-04"), nolint defsWithUnderscore]
alias toSimplicialObject_revIso := toSimplicialObjectRevIso

/-- Hom component of `toSimplicialObjectRevIso` at an arbitrary simplex. -/
@[simp]
theorem toSimplicialObject_revIso_hom_app (X : Data C)
    (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialObjectRevIso (C := C) X).hom.app Δ = 𝟙 _ :=
  rfl

/-- Inverse component of `toSimplicialObjectRevIso` at an arbitrary simplex. -/
@[simp]
theorem toSimplicialObject_revIso_inv_app (X : Data C)
    (Δ : SimplexCategoryᵒᵖ) :
    (toSimplicialObjectRevIso (C := C) X).inv.app Δ = 𝟙 _ :=
  rfl

/-- Hom component of `toSimplicialObjectRevIso` at `op (mk n)`. -/
@[simp]
theorem toSimplicialObject_revIso_hom_app_mk (X : Data C) (n : ℕ) :
    (toSimplicialObjectRevIso (C := C) X).hom.app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  rfl

/-- Inverse component of `toSimplicialObjectRevIso` at `op (mk n)`. -/
@[simp]
theorem toSimplicialObject_revIso_inv_app_mk (X : Data C) (n : ℕ) :
    (toSimplicialObjectRevIso (C := C) X).inv.app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  rfl

/-- Functorial comparison: reversal commutes with `toSimplicialFunctor` and `opFunctor`.

The component at `X` is the accepted `toSimplicialObjectRevIso X`. -/
noncomputable def toSimplicialFunctorRevIso :
    (revFunctor (C := C)) ⋙ (toSimplicialFunctor (C := C)) ≅
      (toSimplicialFunctor (C := C)) ⋙ (SimplicialObject.opFunctor (C := C)) :=
  NatIso.ofComponents
    (fun X => toSimplicialObjectRevIso (C := C) X)
    (fun {X Y} f => by
      ext Δ
      obtain ⟨Δ⟩ := Δ
      rw [NatTrans.comp_app, NatTrans.comp_app]
      rw [toSimplicialObject_revIso_hom_app, toSimplicialObject_revIso_hom_app]
      rw [Functor.comp_map, Functor.comp_map]
      rw [toSimplicialFunctor_map_app_mk, revFunctor_map_app]
      rw [SimplicialObject.opFunctor_map_app, toSimplicialFunctor_map_app_mk]
      change f.app Δ.len ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 _ ≫ f.app Δ.len ≫ 𝟙 _)
      simp only [Category.comp_id, Category.id_comp])

/-- Hom component of `toSimplicialFunctorRevIso` at an arbitrary simplex. -/
@[simp]
theorem toSimplicialFunctorRevIso_hom_app (X : Data C)
    (Δ : SimplexCategoryᵒᵖ) :
    ((toSimplicialFunctorRevIso (C := C)).hom.app X).app Δ = 𝟙 _ :=
  rfl

/-- Inverse component of `toSimplicialFunctorRevIso` at an arbitrary simplex. -/
@[simp]
theorem toSimplicialFunctorRevIso_inv_app (X : Data C)
    (Δ : SimplexCategoryᵒᵖ) :
    ((toSimplicialFunctorRevIso (C := C)).inv.app X).app Δ = 𝟙 _ :=
  rfl

/-- Hom component of `toSimplicialFunctorRevIso` at `op (mk n)`. -/
@[simp]
theorem toSimplicialFunctorRevIso_hom_app_mk (X : Data C) (n : ℕ) :
    ((toSimplicialFunctorRevIso (C := C)).hom.app X).app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  rfl

/-- Inverse component of `toSimplicialFunctorRevIso` at `op (mk n)`. -/
@[simp]
theorem toSimplicialFunctorRevIso_inv_app_mk (X : Data C) (n : ℕ) :
    ((toSimplicialFunctorRevIso (C := C)).inv.app X).app
        (op (SimplexCategory.mk n)) = 𝟙 _ :=
  rfl

end Data
end SimplicialObject
end CategoryTheory

end
