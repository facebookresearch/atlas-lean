/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.DataExtraDegeneracy
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRightExtraDegeneracy
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRightExtraDegeneracy
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
Transport of left- and right-handed `Data`-level extra degeneracies to genuine
augmented simplicial objects, reusing the generic `Data`-to-simplicial
comparison without reproving simplicial identities.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory
namespace SimplicialObject
namespace Data
namespace Augmented

variable {C : Type u} [Category.{v} C]

/--
Transport a left data-level extra degeneracy to Mathlib's augmented simplicial-object structure.
The underlying section `s'` and each extra degeneracy `s n` are the same morphisms.
-/
noncomputable def ExtraDegeneracy.toSimplicial {X : Augmented C}
    (ed : ExtraDegeneracy X) :
    SimplicialObject.Augmented.ExtraDegeneracy X.toSimplicialAugmented where
  s' := by
    have hR : X.toSimplicialAugmented.right = X.right := rfl
    have h0 : X.toSimplicialAugmented.left _⦋0⦌ = X.left.obj 0 := rfl
    exact hR ▸ h0 ▸ ed.s'
  s n := by
    have h0 : X.toSimplicialAugmented.left _⦋n⦌ = X.left.obj n := rfl
    have h1 : X.toSimplicialAugmented.left _⦋n + 1⦌ = X.left.obj (n + 1) := rfl
    exact h0 ▸ h1 ▸ ed.s n
  s'_comp_ε := by
    rw [toSimplicialAugmented_hom_app_mk]
    exact ed.s'_comp_ε
  s₀_comp_δ₁ := by
    have hδ : (toSimplicialAugmented X).left.δ (1 : Fin 2) = X.left.δ (1 : Fin 2) := by
      have h1 : (toSimplicialAugmented X).left.δ (1 : Fin 2) =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ (1 : Fin 2) := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ (1 : Fin 2) =
          (drop.obj X).δ (1 : Fin 2) := toSimplicialAugmented_left_δ X (1 : Fin 2)
      have h3 : (drop.obj X).δ (1 : Fin 2) = X.left.δ (1 : Fin 2) := rfl
      exact h1.trans (h2.trans h3)
    have h_hom : (toSimplicialAugmented X).hom.app (op ⦋0⦌) = X.hom.app 0 :=
      toSimplicialAugmented_hom_app_mk X 0
    rw [hδ, h_hom]
    exact ed.s₀_comp_δ₁
  s_comp_δ₀ := by
    intro n
    have hδ : (toSimplicialAugmented X).left.δ (0 : Fin (n + 2)) = X.left.δ (0 : Fin (n + 2)) := by
      have h1 : (toSimplicialAugmented X).left.δ (0 : Fin (n + 2)) =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ (0 : Fin (n + 2)) := rfl
      have h2 :
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ
            (0 : Fin (n + 2)) =
          (drop.obj X).δ (0 : Fin (n + 2)) :=
        toSimplicialAugmented_left_δ X (0 : Fin (n + 2))
      have h3 : (drop.obj X).δ (0 : Fin (n + 2)) = X.left.δ (0 : Fin (n + 2)) := rfl
      exact h1.trans (h2.trans h3)
    rw [hδ]
    exact ed.s_comp_δ₀ n
  s_comp_δ := by
    intro n i
    have hδ_succ : (toSimplicialAugmented X).left.δ i.succ = X.left.δ i.succ := by
      have h1 : (toSimplicialAugmented X).left.δ i.succ =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i.succ := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i.succ =
          (drop.obj X).δ i.succ := toSimplicialAugmented_left_δ X i.succ
      have h3 : (drop.obj X).δ i.succ = X.left.δ i.succ := rfl
      exact h1.trans (h2.trans h3)
    have hδ : (toSimplicialAugmented X).left.δ i = X.left.δ i := by
      have h1 : (toSimplicialAugmented X).left.δ i =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i =
          (drop.obj X).δ i := toSimplicialAugmented_left_δ X i
      have h3 : (drop.obj X).δ i = X.left.δ i := rfl
      exact h1.trans (h2.trans h3)
    rw [hδ_succ, hδ]
    exact ed.s_comp_δ n i
  s_comp_σ := by
    intro n i
    have hσ_succ : (toSimplicialAugmented X).left.σ i.succ = X.left.σ i.succ := by
      have h1 : (toSimplicialAugmented X).left.σ i.succ =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i.succ := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i.succ =
          (drop.obj X).σ i.succ := toSimplicialAugmented_left_σ X i.succ
      have h3 : (drop.obj X).σ i.succ = X.left.σ i.succ := rfl
      exact h1.trans (h2.trans h3)
    have hσ : (toSimplicialAugmented X).left.σ i = X.left.σ i := by
      have h1 : (toSimplicialAugmented X).left.σ i =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i =
          (drop.obj X).σ i := toSimplicialAugmented_left_σ X i
      have h3 : (drop.obj X).σ i = X.left.σ i := rfl
      exact h1.trans (h2.trans h3)
    rw [hσ_succ, hσ]
    exact ed.s_comp_σ n i

@[simp]
theorem ExtraDegeneracy.toSimplicial_s' {X : Augmented C} (ed : ExtraDegeneracy X) :
    ed.toSimplicial.s' = ed.s' :=
  rfl

@[simp]
theorem ExtraDegeneracy.toSimplicial_s {X : Augmented C} (ed : ExtraDegeneracy X) (n : ℕ) :
    ed.toSimplicial.s n = ed.s n :=
  rfl

/--
Transport a right data-level extra degeneracy to the augmented simplicial-object right structure.
The underlying section `s'` and each extra degeneracy `s n` are the same morphisms.
-/
noncomputable def RightExtraDegeneracy.toSimplicial {X : Augmented C}
    (ed : RightExtraDegeneracy X) :
    SimplicialObject.Augmented.RightExtraDegeneracy X.toSimplicialAugmented where
  s' := by
    have hR : X.toSimplicialAugmented.right = X.right := rfl
    have h0 : X.toSimplicialAugmented.left _⦋0⦌ = X.left.obj 0 := rfl
    exact hR ▸ h0 ▸ ed.s'
  s n := by
    have h0 : X.toSimplicialAugmented.left _⦋n⦌ = X.left.obj n := rfl
    have h1 : X.toSimplicialAugmented.left _⦋n + 1⦌ = X.left.obj (n + 1) := rfl
    exact h0 ▸ h1 ▸ ed.s n
  s'_comp_ε := by
    rw [toSimplicialAugmented_hom_app_mk]
    exact ed.s'_comp_ε
  s₀_comp_δ₀ := by
    have hδ : (toSimplicialAugmented X).left.δ (0 : Fin 2) = X.left.δ (0 : Fin 2) := by
      have h1 : (toSimplicialAugmented X).left.δ (0 : Fin 2) =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ (0 : Fin 2) := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ (0 : Fin 2) =
          (drop.obj X).δ (0 : Fin 2) := toSimplicialAugmented_left_δ X (0 : Fin 2)
      have h3 : (drop.obj X).δ (0 : Fin 2) = X.left.δ (0 : Fin 2) := rfl
      exact h1.trans (h2.trans h3)
    have h_hom : (toSimplicialAugmented X).hom.app (op ⦋0⦌) = X.hom.app 0 :=
      toSimplicialAugmented_hom_app_mk X 0
    rw [hδ, h_hom]
    exact ed.s₀_comp_δ₀
  s_comp_δ_last := by
    intro n
    have hδ : (toSimplicialAugmented X).left.δ (Fin.last (n + 1) : Fin (n + 2)) =
        X.left.δ (Fin.last (n + 1) : Fin (n + 2)) := by
      have h1 : (toSimplicialAugmented X).left.δ (Fin.last (n + 1) : Fin (n + 2)) =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ
            (Fin.last (n + 1) : Fin (n + 2)) := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ
            (Fin.last (n + 1) : Fin (n + 2)) =
          (drop.obj X).δ (Fin.last (n + 1) : Fin (n + 2)) :=
        toSimplicialAugmented_left_δ X (Fin.last (n + 1) : Fin (n + 2))
      have h3 : (drop.obj X).δ (Fin.last (n + 1) : Fin (n + 2)) =
          X.left.δ (Fin.last (n + 1) : Fin (n + 2)) := rfl
      exact h1.trans (h2.trans h3)
    rw [hδ]
    exact ed.s_comp_δ_last n
  s_comp_δ := by
    intro n i
    have hδ_castSucc : (toSimplicialAugmented X).left.δ i.castSucc =
        X.left.δ i.castSucc := by
      have h1 : (toSimplicialAugmented X).left.δ i.castSucc =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i.castSucc := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i.castSucc =
          (drop.obj X).δ i.castSucc := toSimplicialAugmented_left_δ X i.castSucc
      have h3 : (drop.obj X).δ i.castSucc = X.left.δ i.castSucc := rfl
      exact h1.trans (h2.trans h3)
    have hδ : (toSimplicialAugmented X).left.δ i = X.left.δ i := by
      have h1 : (toSimplicialAugmented X).left.δ i =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).δ i =
          (drop.obj X).δ i := toSimplicialAugmented_left_δ X i
      have h3 : (drop.obj X).δ i = X.left.δ i := rfl
      exact h1.trans (h2.trans h3)
    rw [hδ_castSucc, hδ]
    exact ed.s_comp_δ n i
  s_comp_σ := by
    intro n i
    have hσ_castSucc : (toSimplicialAugmented X).left.σ i.castSucc =
        X.left.σ i.castSucc := by
      have h1 : (toSimplicialAugmented X).left.σ i.castSucc =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i.castSucc := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i.castSucc =
          (drop.obj X).σ i.castSucc := toSimplicialAugmented_left_σ X i.castSucc
      have h3 : (drop.obj X).σ i.castSucc = X.left.σ i.castSucc := rfl
      exact h1.trans (h2.trans h3)
    have hσ : (toSimplicialAugmented X).left.σ i = X.left.σ i := by
      have h1 : (toSimplicialAugmented X).left.σ i =
          (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i := rfl
      have h2 : (SimplicialObject.Augmented.drop.obj (toSimplicialAugmented X)).σ i =
          (drop.obj X).σ i := toSimplicialAugmented_left_σ X i
      have h3 : (drop.obj X).σ i = X.left.σ i := rfl
      exact h1.trans (h2.trans h3)
    rw [hσ_castSucc, hσ]
    exact ed.s_comp_σ n i

@[simp]
theorem RightExtraDegeneracy.toSimplicial_s' {X : Augmented C} (ed : RightExtraDegeneracy X) :
    ed.toSimplicial.s' = ed.s' :=
  rfl

@[simp]
theorem RightExtraDegeneracy.toSimplicial_s {X : Augmented C} (ed : RightExtraDegeneracy X)
    (n : ℕ) : ed.toSimplicial.s n = ed.s n :=
  rfl

end Augmented
end Data
end SimplicialObject
end CategoryTheory

end
