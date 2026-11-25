/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.LeftDecalageOperators
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The actual extra degeneracy of the original one-sided decalage

The original first simplicial degeneracy duplicates the distinguished
new vertex. All extra-degeneracy equations are proved from the original
simplex operators, so the resulting contraction retains the entire
original diagram and its original zero-degree augmentation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section

noncomputable section
universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.LeftDecalage

variable {C : Type u} [Category.{v} C]

/-- The augmentation section is the actual original first degeneracy. -/
def sectionZero (W : SimplicialObject C) : (augmented W).right ⟶ (augmented W).left _⦋0⦌ :=
  W.map (SimplexCategory.σ (0 : Fin 1)).op

/-- Every extra degeneracy duplicates the actual original distinguished first vertex. -/
def extraMap (W : SimplicialObject C) (n : ℕ) :
    (augmented W).left _⦋n⦌ ⟶ (augmented W).left _⦋n + 1⦌ :=
  W.map (SimplexCategory.σ (0 : Fin (n + 2))).op

set_option backward.isDefEq.respectTransparency false in
/-- The genuine original shifted diagram has the actual extra-degeneracy structure. -/
def extraDegeneracy (W : SimplicialObject C) : (augmented W).ExtraDegeneracy where
  s' := sectionZero W
  s := extraMap W
  s'_comp_ε := by
    change W.map (SimplexCategory.σ (0 : Fin 1)).op ≫ W.map (firstVertex.app _).op = _
    rw [← W.map_comp]
    have he : firstVertex.app (SimplexCategory.mk 0) ≫ SimplexCategory.σ (0 : Fin 1) =
        𝟙 (SimplexCategory.mk 0) := by ext i; fin_cases i; rfl
    rw [← op_comp, he]
    exact W.map_id _
  s₀_comp_δ₁ := by
    change W.map (SimplexCategory.σ (0 : Fin 2)).op ≫
        W.map (ordinal.map (SimplexCategory.δ (1 : Fin 2))).op =
      W.map (firstVertex.app _).op ≫ W.map (SimplexCategory.σ (0 : Fin 1)).op
    rw [← W.map_comp, ← W.map_comp, ← op_comp, ← op_comp]
    apply congrArg W.map
    apply Quiver.Hom.unop_inj
    rw [ordinal_delta]
    ext i
    fin_cases i <;> rfl
  s_comp_δ₀ n := by
    change W.map (SimplexCategory.σ (0 : Fin (n + 2))).op ≫
      W.map (ordinal.map (SimplexCategory.δ (0 : Fin (n + 2)))).op = _
    rw [ordinal_delta, ← W.map_comp, ← op_comp]
    have he : SimplexCategory.δ (0 : Fin (n + 2)).succ ≫
        SimplexCategory.σ (0 : Fin (n + 2)) = 𝟙 (SimplexCategory.mk (n + 1)) :=
      SimplexCategory.δ_comp_σ_succ
    rw [he]
    exact W.map_id _
  s_comp_δ n i := by
    change W.map (SimplexCategory.σ (0 : Fin (n + 3))).op ≫
        W.map (ordinal.map (SimplexCategory.δ i.succ)).op =
      W.map (ordinal.map (SimplexCategory.δ i)).op ≫
        W.map (SimplexCategory.σ (0 : Fin (n + 2))).op
    rw [ordinal_delta, ordinal_delta, ← W.map_comp, ← W.map_comp, ← op_comp, ← op_comp]
    apply congrArg W.map
    apply Quiver.Hom.unop_inj
    change SimplexCategory.δ i.succ.succ ≫ SimplexCategory.σ (0 : Fin (n + 3)) =
      SimplexCategory.σ (0 : Fin (n + 2)) ≫ SimplexCategory.δ i.succ
    simpa only [Fin.castSucc_zero] using
      (SimplexCategory.δ_comp_σ_of_gt (i := i.succ) (j := (0 : Fin (n + 2)))
        (by change 0 < i.val + 1; omega))
  s_comp_σ n i := by
    change W.map (SimplexCategory.σ (0 : Fin (n + 2))).op ≫
        W.map (ordinal.map (SimplexCategory.σ i.succ)).op =
      W.map (ordinal.map (SimplexCategory.σ i)).op ≫
        W.map (SimplexCategory.σ (0 : Fin (n + 3))).op
    rw [ordinal_sigma, ordinal_sigma, ← W.map_comp, ← W.map_comp, ← op_comp, ← op_comp]
    apply congrArg W.map
    apply Quiver.Hom.unop_inj
    change SimplexCategory.σ i.succ.succ ≫ SimplexCategory.σ (0 : Fin (n + 2)) =
      SimplexCategory.σ (0 : Fin (n + 3)) ≫ SimplexCategory.σ i.succ
    simpa only [Fin.castSucc_zero] using
      (SimplexCategory.σ_comp_σ (i := (0 : Fin (n + 2))) (j := i.succ) (Fin.zero_le _)).symm

end CategoryTheory.SimplicialObject.LeftDecalage
