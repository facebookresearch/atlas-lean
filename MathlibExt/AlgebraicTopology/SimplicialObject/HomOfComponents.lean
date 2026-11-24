/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Equivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# simplicial maps from compatible degree maps

Faces and degeneracies generate the simplex category. Actual degree maps
that commute with those two families therefore determine a simplicial
morphism. The construction uses the simplex generators-and-relations
equivalence and fully faithful precomposition. No degree map is required to
be invertible, and no additive or homological structure is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}

local notation "E" => SimplexCategoryGenRel.toSimplexCategory
local notation "W" => Functor.obj
  (Functor.whiskeringLeft SimplexCategoryGenRelᵒᵖ SimplexCategoryᵒᵖ C) (Functor.op E)

private def generatorComponent
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (q : SimplexCategoryGenRelᵒᵖ) :
    X.obj (op (Functor.obj E q.unop)) ⟶ Y.obj (op (Functor.obj E q.unop)) :=
  f q.unop.len

private theorem generatorNaturality
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1))
    {a b : SimplexCategoryGenRel} (g : a ⟶ b) :
    X.map (Functor.map E g).op ≫ generatorComponent f (op a) =
      generatorComponent f (op b) ≫ Y.map (Functor.map E g).op := by
  let P : MorphismProperty SimplexCategoryGenRel := fun a b g ↦
    X.map (Functor.map E g).op ≫ generatorComponent f (op a) =
      generatorComponent f (op b) ≫ Y.map (Functor.map E g).op
  change P g
  refine SimplexCategoryGenRel.hom_induction P ?_ ?_ ?_ g
  · intro n
    simp only [P, Functor.map_id, op_id, Category.id_comp, Category.comp_id]
  · intro n m g i hg
    have sg : CommSq (X.map (Functor.map E g).op)
        (generatorComponent f (op (SimplexCategoryGenRel.mk m)))
        (generatorComponent f (op (SimplexCategoryGenRel.mk n)))
        (Y.map (Functor.map E g).op) := ⟨hg⟩
    have sd : CommSq (X.map (Functor.map E (SimplexCategoryGenRel.δ i)).op)
        (generatorComponent f (op (SimplexCategoryGenRel.mk (m + 1))))
        (generatorComponent f (op (SimplexCategoryGenRel.mk m)))
        (Y.map (Functor.map E (SimplexCategoryGenRel.δ i)).op) := by
      constructor
      simpa only [generatorComponent, SimplexCategoryGenRel.mk_len,
        SimplexCategoryGenRel.toSimplexCategory_obj_mk,
        SimplexCategoryGenRel.toSimplexCategory_map_δ, SimplicialObject.δ_def]
        using (hδ i).symm
    have h := (sd.horiz_comp sg).w
    simpa only [P, Functor.map_comp, op_comp, Category.assoc] using h
  · intro n m g i hg
    have sg : CommSq (X.map (Functor.map E g).op)
        (generatorComponent f (op (SimplexCategoryGenRel.mk (m + 1))))
        (generatorComponent f (op (SimplexCategoryGenRel.mk n)))
        (Y.map (Functor.map E g).op) := ⟨hg⟩
    have ss : CommSq (X.map (Functor.map E (SimplexCategoryGenRel.σ i)).op)
        (generatorComponent f (op (SimplexCategoryGenRel.mk m)))
        (generatorComponent f (op (SimplexCategoryGenRel.mk (m + 1))))
        (Y.map (Functor.map E (SimplexCategoryGenRel.σ i)).op) := by
      constructor
      simpa only [generatorComponent, SimplexCategoryGenRel.mk_len,
        SimplexCategoryGenRel.toSimplexCategory_obj_mk,
        SimplexCategoryGenRel.toSimplexCategory_map_σ, SimplicialObject.σ_def]
        using (hσ i).symm
    have h := (ss.horiz_comp sg).w
    simpa only [P, Functor.map_comp, op_comp, Category.assoc] using h

private def generatorMap
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1)) :
    Functor.obj W X ⟶ Functor.obj W Y where
  app := generatorComponent f
  naturality {_ _} g := generatorNaturality f hδ hσ g.unop

/-- Compatible face and degeneracy squares construct a native
simplicial map, with no invertibility or additive hypothesis. -/
@[no_expose]
def homOfComponents
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1)) :
    X ⟶ Y :=
  Functor.preimage W (generatorMap f hδ hσ)

/-- The constructed simplicial map has the prescribed original components. -/
theorem homOfComponents_app_mk
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1))
    (n : ℕ) : (homOfComponents f hδ hσ).app (op (SimplexCategory.mk n)) = f n := by
  have h := congr_app (Functor.map_preimage W (generatorMap f hδ hσ))
    (op (SimplexCategoryGenRel.mk n))
  exact h

/-- Equality of prescribed degree components determines the native map. -/
theorem homOfComponents_ext
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1))
    (g : X ⟶ Y) (hg : ∀ n, g.app (op (SimplexCategory.mk n)) = f n) :
    g = homOfComponents f hδ hσ := by
  apply NatTrans.ext
  funext q
  obtain ⟨q⟩ := q
  cases q
  exact (hg _).trans (homOfComponents_app_mk f hδ hσ _).symm

/-- Identity degree maps give the identity simplicial map. -/
@[simp]
theorem homOfComponents_id (X : SimplicialObject C) :
    homOfComponents (fun n => 𝟙 (X.obj (op (SimplexCategory.mk n))))
      (by intro n i; simp) (by intro n i; simp) = 𝟙 X := by
  apply NatTrans.ext
  funext q
  obtain ⟨q⟩ := q
  cases q with
  | mk n =>
    change (homOfComponents (fun q => 𝟙 (X.obj (op (SimplexCategory.mk q))))
      (by intro q i; simp) (by intro q i; simp)).app (op (SimplexCategory.mk n)) = 𝟙 _
    exact homOfComponents_app_mk _ _ _ n

/-- Composition of the prescribed degree maps gives composition of
the constructed native simplicial maps. -/
@[reassoc]
theorem homOfComponents_comp {Z : SimplicialObject C}
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1))
    (g : ∀ n : ℕ, Y.obj (op (SimplexCategory.mk n)) ⟶
      Z.obj (op (SimplexCategory.mk n)))
    (gδ : ∀ {n : ℕ} (i : Fin (n + 2)), g (n + 1) ≫ Z.δ i = Y.δ i ≫ g n)
    (gσ : ∀ {n : ℕ} (i : Fin (n + 1)), g n ≫ Z.σ i = Y.σ i ≫ g (n + 1)) :
    homOfComponents f hδ hσ ≫ homOfComponents g gδ gσ =
      homOfComponents (fun n => f n ≫ g n)
        (by intro n i; rw [Category.assoc, gδ, ← Category.assoc, hδ, Category.assoc])
        (by intro n i; rw [Category.assoc, gσ, ← Category.assoc, hσ, Category.assoc]) := by
  apply NatTrans.ext
  funext q
  obtain ⟨q⟩ := q
  cases q with
  | mk n =>
    change (homOfComponents f hδ hσ).app (op (SimplexCategory.mk n)) ≫
        (homOfComponents g gδ gσ).app (op (SimplexCategory.mk n)) =
      (homOfComponents (fun q => f q ≫ g q)
        (by intro q i; rw [Category.assoc, gδ, ← Category.assoc, hδ, Category.assoc])
        (by intro q i; rw [Category.assoc, gσ, ← Category.assoc, hσ, Category.assoc])).app
          (op (SimplexCategory.mk n))
    rw [homOfComponents_app_mk, homOfComponents_app_mk, homOfComponents_app_mk]

end CategoryTheory.SimplicialObject
