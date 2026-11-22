/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeHomotopyOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopy

/-!
# The native row-zero contraction has the original interval cut operator

The complete shifted face/extra-degeneracy/degeneracy operator restricts
to the original row-zero interval simplex. The proof compares every
original ordinal vertex and retains the same cut index.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

private theorem shifted_apply_succ {a b : SimplexCategory} (f : a ⟶ b)
    (j : Fin (a.len + 1)) :
    (SimplicialObject.LeftDecalage.ordinal.map f).toOrderHom j.succ = (f.toOrderHom j).succ := rfl

private theorem shifted_apply_zero {a b : SimplexCategory} (f : a ⟶ b) :
    (SimplicialObject.LeftDecalage.ordinal.map f).toOrderHom 0 = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original row-zero native contraction operator is precisely the same original interval cut. -/
theorem nativeHomotopyOrdinal_row_zero (n : ℕ) (i : Fin (n + 1)) :
    SimplicialObject.LeftDecalage.rightBlock.app (SimplexCategory.mk n) ≫
        SimplicialObject.LeftDecalage.ordinal.map (SimplexCategory.δ i.succ) ≫
        nativeHomotopyOrdinal n i ≫ SimplicialObject.LeftDecalage.ordinal.map
          (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0) =
      SSet.stdSimplex.objEquiv (SSet.stdSimplex.objMk₁.{0} i.succ) := by
  ext j
  dsimp only [nativeHomotopyOrdinal, SSet.stdSimplex.objMk₁,
    SimplicialObject.LeftDecalage.rightBlock]
  change ((SimplicialObject.LeftDecalage.ordinal.map
      (SimplexCategory.const (SimplexCategory.mk n) (SimplexCategory.mk 0) 0)).toOrderHom
    ((SimplicialObject.LeftDecalage.ordinal.map
      (SimplexCategory.δ₀Iter i.val (n := i.rev.val) (m := n) (by simp [Fin.val_rev]; omega))).toOrderHom
      ((SimplexCategory.σ (0 : Fin (i.rev.val + 2))).toOrderHom
        ((SimplicialObject.LeftDecalage.ordinal.map
          (SimplexCategory.σ₀Iter i.val (n := i.rev.val + 1) (m := n + 1)
            (by simp [Fin.val_rev]; omega))).toOrderHom
          ((SimplicialObject.LeftDecalage.ordinal.map (SimplexCategory.δ i.succ)).toOrderHom j.succ))))).val =
    (if j.castSucc < i.succ then (0 : Fin 2) else 1).val
  rw [shifted_apply_succ, shifted_apply_succ]
  by_cases h : j ≤ i
  · simp [SimplexCategory.δ₀Iter, SimplexCategory.σ₀Iter, SimplexCategory.δ,
      SimplexCategory.σ, OrderHom.coe_mk, Fin.succAbove, Fin.predAbove, h]
    rw [shifted_apply_zero, shifted_apply_zero]
  · simp [SimplexCategory.δ₀Iter, SimplexCategory.σ₀Iter, SimplexCategory.δ,
      SimplexCategory.σ, OrderHom.coe_mk, Fin.succAbove, Fin.predAbove, h]
    have hj : i.val < j.val := Fin.lt_def.mp (lt_of_not_ge h)
    have hpos : ¬j.val + 1 < i.val := by omega
    rw [ite_eq_right hpos]
    have hp : 0 < j.val + 1 - i.val := by omega
    obtain ⟨k, hk⟩ := (⟨j.val + 1 - i.val, by
      have hjBound : j.val ≤ n := j.is_le
      simp only [Fin.val_rev]
      omega⟩ : Fin (i.rev.val + 2)).eq_succ_of_ne_zero
      (by intro h0; have hv := congrArg Fin.val h0; simp at hv; omega)
    rw [hk, shifted_apply_succ, shifted_apply_succ]
    rfl

end SimplicialSpace.LeftDecalageObject
