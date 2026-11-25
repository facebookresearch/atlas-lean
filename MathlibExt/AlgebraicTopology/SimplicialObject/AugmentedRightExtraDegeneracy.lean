/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedWhiskering

/-!
# Right extra degeneracies for augmented simplicial objects

This module provides the mirrored right-handed extra-degeneracy structure:
the distinguished identity uses the last face `Fin.last (n + 1)`, while the
remaining face and degeneracy compatibilities use `Fin.castSucc`.
`RightExtraDegeneracy.map` and `RightExtraDegeneracy.ofIso` transport the
structure along functors and isomorphisms of augmented objects. Simplex
reversal converts it to Mathlib's left-handed
`SimplicialObject.Augmented.ExtraDegeneracy` contraction API, so its
homotopy consequences are inherited rather than reproved.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe v u v' u'

namespace CategoryTheory
namespace SimplicialObject
namespace Augmented

variable {C : Type u} [Category.{v} C]

/--
Right-handed extra-degeneracy structure for augmented simplicial objects,
mirroring `SimplicialObject.Augmented.ExtraDegeneracy` with distinguished terminal face
`Fin.last (n + 1)` and nonterminal equations using `Fin.castSucc`.
-/
@[ext]
structure RightExtraDegeneracy (X : Augmented C) where
  /-- A section from the augmentation point to degree zero -/
  s' : X.right ⟶ X.left _⦋0⦌
  /-- Extra degeneracies `X_n ⟶ X_{n+1}` -/
  s : ∀ n : ℕ, X.left _⦋n⦌ ⟶ X.left _⦋n + 1⦌
  /-- Section / augmentation identity -/
  s'_comp_ε : s' ≫ X.hom.app (op ⦋0⦌) = 𝟙 X.right := by cat_disch
  /-- Degree-zero compatibility with face `0` -/
  s₀_comp_δ₀ : s 0 ≫ X.left.δ 0 = X.hom.app (op ⦋0⦌) ≫ s' := by cat_disch
  /-- Distinguished terminal-face identity -/
  s_comp_δ_last : ∀ n : ℕ, s n ≫ X.left.δ (Fin.last (n + 1) : Fin (n + 2)) = 𝟙 _ := by cat_disch
  /-- Compatibility with all nonterminal faces -/
  s_comp_δ :
    ∀ (n : ℕ) (i : Fin (n + 2)), s (n + 1) ≫ X.left.δ i.castSucc = X.left.δ i ≫ s n := by
    cat_disch
  /-- Compatibility with all nonterminal degeneracies -/
  s_comp_σ :
    ∀ (n : ℕ) (i : Fin (n + 1)), s n ≫ X.left.σ i.castSucc = X.left.σ i ≫ s (n + 1) := by
    cat_disch

namespace RightExtraDegeneracy

attribute [reassoc] s₀_comp_δ₀ s_comp_δ s_comp_σ
attribute [reassoc (attr := simp)] s'_comp_ε s_comp_δ_last

def map {D : Type u'} [Category.{v'} D] {X : Augmented C}
    (ed : RightExtraDegeneracy X) (F : C ⥤ D) :
    RightExtraDegeneracy ((whiskeringObj C D F).obj X) where
  s' := F.map ed.s'
  s n := F.map (ed.s n)
  s'_comp_ε := by
    rw [whiskeringObj_obj_hom_app]
    change F.map ed.s' ≫ F.map (X.hom.app (op ⦋0⦌)) = 𝟙 (F.obj X.right)
    rw [← F.map_comp, ed.s'_comp_ε, F.map_id]
  s₀_comp_δ₀ := by
    rw [whiskeringObj_obj_left_δ, whiskeringObj_obj_hom_app]
    change F.map (ed.s 0) ≫ F.map (X.left.δ 0) =
        F.map (X.hom.app (op ⦋0⦌)) ≫ F.map ed.s'
    rw [← F.map_comp, ed.s₀_comp_δ₀, F.map_comp]
  s_comp_δ_last n := by
    rw [whiskeringObj_obj_left_δ]
    change F.map (ed.s n) ≫ F.map (X.left.δ (Fin.last (n + 1))) =
        𝟙 (F.obj (X.left _⦋n⦌))
    rw [← F.map_comp, ed.s_comp_δ_last, F.map_id]
  s_comp_δ n i := by
    rw [whiskeringObj_obj_left_δ, whiskeringObj_obj_left_δ]
    change F.map (ed.s (n + 1)) ≫ F.map (X.left.δ i.castSucc) =
        F.map (X.left.δ i) ≫ F.map (ed.s n)
    rw [← F.map_comp, ← F.map_comp, ed.s_comp_δ]
  s_comp_σ n i := by
    rw [whiskeringObj_obj_left_σ, whiskeringObj_obj_left_σ]
    change F.map (ed.s n) ≫ F.map (X.left.σ i.castSucc) =
        F.map (X.left.σ i) ≫ F.map (ed.s (n + 1))
    rw [← F.map_comp, ← F.map_comp, ed.s_comp_σ]

@[simp]
theorem map_s' {D : Type u'} [Category.{v'} D] {X : Augmented C}
    (ed : RightExtraDegeneracy X) (F : C ⥤ D) :
    (ed.map F).s' = F.map ed.s' := rfl

@[simp]
theorem map_s {D : Type u'} [Category.{v'} D] {X : Augmented C}
    (ed : RightExtraDegeneracy X) (F : C ⥤ D) (n : ℕ) :
    (ed.map F).s n = F.map (ed.s n) := rfl

/--
If `X` and `Y` are isomorphic augmented simplicial objects, then a right extra
degeneracy for `X` gives also a right extra degeneracy for `Y`.
-/
def ofIso {X Y : Augmented C} (e : X ≅ Y) (ed : RightExtraDegeneracy X) :
    RightExtraDegeneracy Y where
  s' := (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op ⦋0⦌)
  s n := (drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op ⦋n + 1⦌)
  s'_comp_ε := by
    simpa [w₀] using (point.mapIso e).inv_hom_id
  s₀_comp_δ₀ := by
    simp [← SimplicialObject.δ_naturality, s₀_comp_δ₀_assoc, w₀_assoc]
  s_comp_δ_last n := by
    simpa [← SimplicialObject.δ_naturality] using
      congr_app (drop.mapIso e).inv_hom_id (op ⦋n⦌)
  s_comp_δ n i := by
    simp [← SimplicialObject.δ_naturality, s_comp_δ_assoc,
      ← SimplicialObject.δ_naturality_assoc]
  s_comp_σ n i := by
    simp [← SimplicialObject.σ_naturality, s_comp_σ_assoc,
      ← SimplicialObject.σ_naturality_assoc]

@[simp]
theorem ofIso_s' {X Y : Augmented C} (e : X ≅ Y) (ed : RightExtraDegeneracy X) :
    (ed.ofIso e).s' = (point.mapIso e).inv ≫ ed.s' ≫ (drop.mapIso e).hom.app (op ⦋0⦌) :=
  rfl

@[simp]
theorem ofIso_s {X Y : Augmented C} (e : X ≅ Y) (ed : RightExtraDegeneracy X) (n : ℕ) :
    (ed.ofIso e).s n =
      (drop.mapIso e).inv.app (op ⦋n⦌) ≫ ed.s n ≫ (drop.mapIso e).hom.app (op ⦋n + 1⦌) :=
  rfl

end RightExtraDegeneracy

end Augmented
end SimplicialObject
end CategoryTheory

end
