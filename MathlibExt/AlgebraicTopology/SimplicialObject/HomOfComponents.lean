/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Simplicial morphisms specified by degree maps

In an arbitrary category C, maps f_n : X_n → Y_n between the terms of two simplicial objects
determine a simplicial morphism when they commute with every face and degeneracy. The face
equations are f_(n+1) ≫ δ_i^Y = δ_i^X ≫ f_n; the degeneracy equations are f_n ≫ σ_i^Y = σ_i^X
≫ f_(n+1).

The resulting morphism has exactly the specified components, is uniquely determined by them,
and respects identities and composition. Naturality follows from the native generation theorem for
morphisms by faces and degeneracies.

See Mac Lane, *Categories for the Working Mathematician*, Chapter VII, for simplicial objects.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}

/-- Let X and Y be simplicial objects in a category C. Suppose f_n : X_n ⟶ Y_n satisfies f_(n+1) ≫
δ_i^Y = δ_i^X ≫ f_n for i : Fin (n + 2), and f_n ≫ σ_i^Y = σ_i^X ≫ f_(n+1) for i : Fin (n +
1). The family f defines a morphism homOfComponents f hδ hσ : X ⟶ Y whose component at op ⦋n⦌
is f_n. The face and degeneracy equations give its naturality for every simplex-category
morphism. -/
def homOfComponents
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1)) :
    X ⟶ Y where
  app q := f q.unop.len
  naturality {a b} g := by
    let P : MorphismProperty SimplexCategoryᵒᵖ :=
      MorphismProperty.naturalityProperty
        (fun q : SimplexCategoryᵒᵖ => f q.unop.len)
    have hP : P.unop = ⊤ := by
      apply SimplexCategory.morphismProperty_eq_top
      · intro n i
        change X.δ i ≫ f n = f (n + 1) ≫ Y.δ i
        exact (hδ i).symm
      · intro n i
        change X.σ i ≫ f (n + 1) = f n ≫ Y.σ i
        exact (hσ i).symm
    have hg : P.unop g.unop := by
      rw [hP]
      trivial
    exact hg

/-- Let X and Y be simplicial objects in a category C. Suppose f_n : X_n ⟶ Y_n satisfies f_(n+1) ≫
δ_i^Y = δ_i^X ≫ f_n for i : Fin (n + 2), and f_n ≫ σ_i^Y = σ_i^X ≫ f_(n+1) for i : Fin (n +
1). For every n : ℕ, the component of homOfComponents f hδ hσ at op (SimplexCategory.mk n) is
f_n. -/
theorem homOfComponents_app_mk
    (f : ∀ n : ℕ, X.obj (op (SimplexCategory.mk n)) ⟶
      Y.obj (op (SimplexCategory.mk n)))
    (hδ : ∀ {n : ℕ} (i : Fin (n + 2)), f (n + 1) ≫ Y.δ i = X.δ i ≫ f n)
    (hσ : ∀ {n : ℕ} (i : Fin (n + 1)), f n ≫ Y.σ i = X.σ i ≫ f (n + 1))
    (n : ℕ) : (homOfComponents f hδ hσ).app (op (SimplexCategory.mk n)) = f n := rfl

/-- Let X and Y be simplicial objects in a category C. Suppose f_n : X_n ⟶ Y_n satisfies f_(n+1) ≫
δ_i^Y = δ_i^X ≫ f_n for i : Fin (n + 2), and f_n ≫ σ_i^Y = σ_i^X ≫ f_(n+1) for i : Fin (n +
1). If a simplicial map g : X ⟶ Y has component f_n at every op ⦋n⦌, then g = homOfComponents
f hδ hσ. -/
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

/-- For a simplicial object X in any category C, the family f_n = 𝟙 X_n commutes with every face
and degeneracy. The simplicial morphism constructed from this family and these equations
equals 𝟙 X. -/
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

/-- Let X, Y and Z be simplicial objects in a category C. Let f_n : X_n ⟶ Y_n and g_n : Y_n ⟶ Z_n
each commute with all faces and degeneracies, in the equations f_(n+1) ≫ δ_i^Y = δ_i^X ≫ f_n
and f_n ≫ σ_i^Y = σ_i^X ≫ f_(n+1), and the corresponding equations for g. Then the simplicial
map for f followed by that for g equals the map constructed from the components f_n ≫ g_n and
their induced face and degeneracy equations. -/
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
