/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Edgewise
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Reindex

/-!
# Edgewise shell indices for Quillen span flags

The opposite-first edgewise ordinal has a reversed left block and a straight
right block.  This file packages their canonical indices, their behavior
under arbitrary simplex maps and under faces/degeneracies, and the four-point
shell selecting one six-cell Stage flag.  Stage restriction then commutes
strictly with edgewise reindexing.

This is finite-index infrastructure only.  It constructs no raw span, flag,
quotient class, simplicial comparison, realization, additivity, or Q/S
equivalence.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

namespace SimplexCategory

/-- The index in the reversed, first block corresponding to `k`. -/
def edgewiseLeftIndex (a : SimplexCategory)
    (k : Fin (a.len + 1)) : Fin ((edgewiseQ.obj a).len + 1) :=
  (AugmentedSimplexCategory.inl' a a).toOrderHom k.rev

/-- The index in the straight, second block corresponding to `k`. -/
def edgewiseRightIndex (a : SimplexCategory)
    (k : Fin (a.len + 1)) : Fin ((edgewiseQ.obj a).len + 1) :=
  (AugmentedSimplexCategory.inr' a a).toOrderHom k

@[simp]
theorem edgewiseLeftIndex_eq (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    edgewiseLeftIndex a k =
      (k.rev.castAdd (a.len + 1)).cast
        (Nat.succ_add a.len (a.len + 1)) := by
  exact AugmentedSimplexCategory.inl'_eval a a k.rev

@[simp]
theorem edgewiseRightIndex_eq (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    edgewiseRightIndex a k =
      (k.natAdd (a.len + 1)).cast
        (Nat.succ_add a.len (a.len + 1)) := by
  exact AugmentedSimplexCategory.inr'_eval a a k

@[simp]
theorem edgewiseLeftIndex_val (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    (edgewiseLeftIndex a k).val = a.len - k.val := by
  rw [edgewiseLeftIndex_eq]
  simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_rev]
  omega

@[simp]
theorem edgewiseRightIndex_val (a : SimplexCategory)
    (k : Fin (a.len + 1)) :
    (edgewiseRightIndex a k).val = a.len + 1 + k.val := by
  rw [edgewiseRightIndex_eq]
  rfl

/-- The edgewise map carries the reversed left-block index of `k` to the
left-block index of its image. -/
@[simp]
theorem edgewiseQ_map_leftIndex {a b : SimplexCategory} (α : a ⟶ b)
    (k : Fin (a.len + 1)) :
    (edgewiseQ.map α).toOrderHom (edgewiseLeftIndex a k) =
      edgewiseLeftIndex b (α.toOrderHom k) := by
  have h := AugmentedSimplexCategory.inl_comp_tensorHom
    (x₁ := WithInitial.of a) (y₁ := WithInitial.of b)
    (x₂ := WithInitial.of a) (y₂ := WithInitial.of b)
    (rev.map α) α
  change AugmentedSimplexCategory.inl' a a ≫
      AugmentedSimplexCategory.tensorHomOf (rev.map α) α =
    rev.map α ≫ AugmentedSimplexCategory.inl' b b at h
  have h' := DFunLike.congr_fun (congrArg Hom.toOrderHom h) k.rev
  change (edgewiseQ.map α).toOrderHom (edgewiseLeftIndex a k) =
    (AugmentedSimplexCategory.inl' b b).toOrderHom
      ((rev.map α).toOrderHom k.rev) at h'
  simpa only [edgewiseLeftIndex, rev_map_apply, Fin.rev_rev] using h'

/-- The edgewise map carries the straight right-block index of `k` to the
right-block index of its image. -/
@[simp]
theorem edgewiseQ_map_rightIndex {a b : SimplexCategory} (α : a ⟶ b)
    (k : Fin (a.len + 1)) :
    (edgewiseQ.map α).toOrderHom (edgewiseRightIndex a k) =
      edgewiseRightIndex b (α.toOrderHom k) := by
  have h := AugmentedSimplexCategory.inr_comp_tensorHom
    (x₁ := WithInitial.of a) (y₁ := WithInitial.of b)
    (x₂ := WithInitial.of a) (y₂ := WithInitial.of b)
    (rev.map α) α
  change AugmentedSimplexCategory.inr' a a ≫
      AugmentedSimplexCategory.tensorHomOf (rev.map α) α =
    α ≫ AugmentedSimplexCategory.inr' b b at h
  have h' := DFunLike.congr_fun (congrArg Hom.toOrderHom h) k
  change (edgewiseQ.map α).toOrderHom (edgewiseRightIndex a k) =
    (AugmentedSimplexCategory.inr' b b).toOrderHom
      (α.toOrderHom k) at h'
  simpa only [edgewiseRightIndex] using h'

@[simp]
theorem edgewiseQ_map_δ_leftIndex {n : ℕ}
    (q : Fin (n + 2)) (k : Fin (n + 1)) :
    (edgewiseQ.map (δ q)).toOrderHom (edgewiseLeftIndex ⦋n⦌ k) =
      edgewiseLeftIndex ⦋n + 1⦌ (q.succAbove k) := by
  simpa [δ] using edgewiseQ_map_leftIndex (δ q) k

@[simp]
theorem edgewiseQ_map_δ_rightIndex {n : ℕ}
    (q : Fin (n + 2)) (k : Fin (n + 1)) :
    (edgewiseQ.map (δ q)).toOrderHom (edgewiseRightIndex ⦋n⦌ k) =
      edgewiseRightIndex ⦋n + 1⦌ (q.succAbove k) := by
  simpa [δ] using edgewiseQ_map_rightIndex (δ q) k

@[simp]
theorem edgewiseQ_map_σ_leftIndex {n : ℕ}
    (q : Fin (n + 1)) (k : Fin (n + 2)) :
    (edgewiseQ.map (σ q)).toOrderHom
        (edgewiseLeftIndex ⦋n + 1⦌ k) =
      edgewiseLeftIndex ⦋n⦌ (q.predAbove k) := by
  simpa [σ] using edgewiseQ_map_leftIndex (σ q) k

@[simp]
theorem edgewiseQ_map_σ_rightIndex {n : ℕ}
    (q : Fin (n + 1)) (k : Fin (n + 2)) :
    (edgewiseQ.map (σ q)).toOrderHom
        (edgewiseRightIndex ⦋n + 1⦌ k) =
      edgewiseRightIndex ⦋n⦌ (q.predAbove k) := by
  simpa [σ] using edgewiseQ_map_rightIndex (σ q) k

/-- The four vertices of the Stage-3 shell associated to an interval
`k ≤ l`: reversed `l,k`, followed by straight `k,l`. -/
def edgewiseShell (a : SimplexCategory)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (⦋3⦌ : SimplexCategory) ⟶ edgewiseQ.obj a :=
  Hom.mk
    { toFun := fun
        | ⟨0, _⟩ => edgewiseLeftIndex a l
        | ⟨1, _⟩ => edgewiseLeftIndex a k
        | ⟨2, _⟩ => edgewiseRightIndex a k
        | ⟨3, _⟩ => edgewiseRightIndex a l
      monotone' := by
        intro x y hxy
        fin_cases x <;> fin_cases y <;>
          simp only [Fin.le_def, edgewiseLeftIndex_val,
            edgewiseRightIndex_val] at hxy ⊢ <;>
          omega }

@[simp]
theorem edgewiseShell_zero (a : SimplexCategory)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseShell a k l hkl).toOrderHom 0 = edgewiseLeftIndex a l :=
  rfl

@[simp]
theorem edgewiseShell_one (a : SimplexCategory)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseShell a k l hkl).toOrderHom 1 = edgewiseLeftIndex a k :=
  rfl

@[simp]
theorem edgewiseShell_two (a : SimplexCategory)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseShell a k l hkl).toOrderHom 2 = edgewiseRightIndex a k :=
  rfl

@[simp]
theorem edgewiseShell_three (a : SimplexCategory)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseShell a k l hkl).toOrderHom 3 = edgewiseRightIndex a l :=
  rfl

/-- Shell restriction is strictly natural under every simplex map. -/
@[simp]
theorem edgewiseShell_comp_edgewiseQ_map
    {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    edgewiseShell a k l hkl ≫ edgewiseQ.map α =
      edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
        (α.toOrderHom.monotone hkl) := by
  ext r : 3
  fin_cases r
  · rw [comp_toOrderHom]
    change (edgewiseQ.map α).toOrderHom (edgewiseLeftIndex a l) =
      edgewiseLeftIndex b (α.toOrderHom l)
    exact edgewiseQ_map_leftIndex α l
  · rw [comp_toOrderHom]
    change (edgewiseQ.map α).toOrderHom (edgewiseLeftIndex a k) =
      edgewiseLeftIndex b (α.toOrderHom k)
    exact edgewiseQ_map_leftIndex α k
  · rw [comp_toOrderHom]
    change (edgewiseQ.map α).toOrderHom (edgewiseRightIndex a k) =
      edgewiseRightIndex b (α.toOrderHom k)
    exact edgewiseQ_map_rightIndex α k
  · rw [comp_toOrderHom]
    change (edgewiseQ.map α).toOrderHom (edgewiseRightIndex a l) =
      edgewiseRightIndex b (α.toOrderHom l)
    exact edgewiseQ_map_rightIndex α l

@[simp]
theorem edgewiseShell_comp_edgewiseQ_map_δ {n : ℕ}
    (q : Fin (n + 2)) (k l : Fin (n + 1)) (hkl : k ≤ l) :
    edgewiseShell ⦋n⦌ k l hkl ≫ edgewiseQ.map (δ q) =
      edgewiseShell ⦋n + 1⦌ (q.succAbove k) (q.succAbove l)
        ((Fin.succAboveOrderEmb q).monotone hkl) := by
  simpa [δ] using edgewiseShell_comp_edgewiseQ_map (δ q) k l hkl

@[simp]
theorem edgewiseShell_comp_edgewiseQ_map_σ {n : ℕ}
    (q : Fin (n + 1)) (k l : Fin (n + 2)) (hkl : k ≤ l) :
    edgewiseShell ⦋n + 1⦌ k l hkl ≫ edgewiseQ.map (σ q) =
      edgewiseShell ⦋n⦌ (q.predAbove k) (q.predAbove l)
        ((Fin.predAboveOrderHom q).monotone hkl) := by
  simpa [σ] using edgewiseShell_comp_edgewiseQ_map (σ q) k l hkl

end SimplexCategory

namespace CategoryTheory.Waldhausen.SConstruction

open Limits SimplexCategory

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- Reindexing first by an edgewise simplex map and then by a shell equals
restriction to the image shell. -/
theorem reindexStage_edgewiseShell
    {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    reindexStage (C := C) (edgewiseQ.map α) ⋙
        reindexStage (C := C) (edgewiseShell a k l hkl) =
      reindexStage (C := C)
        (edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
          (α.toOrderHom.monotone hkl)) := by
  rw [← reindexStage_comp,
    edgewiseShell_comp_edgewiseQ_map]

@[simp]
theorem reindexStage_edgewiseShell_obj
    {a b : SimplexCategory} (α : a ⟶ b)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l)
    (A : Stage C (edgewiseQ.obj b).len) :
    (reindexStage (C := C) (edgewiseShell a k l hkl)).obj
        ((reindexStage (C := C) (edgewiseQ.map α)).obj A) =
      (reindexStage (C := C)
        (edgewiseShell b (α.toOrderHom k) (α.toOrderHom l)
          (α.toOrderHom.monotone hkl))).obj A := by
  simpa only [Functor.comp_obj] using
    Functor.congr_obj (reindexStage_edgewiseShell (C := C) α k l hkl) A

end CategoryTheory.Waldhausen.SConstruction
