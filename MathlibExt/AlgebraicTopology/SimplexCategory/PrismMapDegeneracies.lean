/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplexCategory.PrismMap

/-!
# Original degeneracies of the functorial simplex prism

The canonical prism lift of an original elementary epi is an elementary epi
at its actual shifted index. These identities identify the arbitrary-epi
prescription with both degeneracy laws of native `SimplicialObject.Homotopy`.
They supplement the existing functorial prism map, without replacing it.
Source proposals only; UNEXECUTED.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.PrismMap

variable {n : ℕ}

theorem sigma_vertex_of_le (i j : Fin (n + 1)) (hij : i ≤ j) :
    (SimplexCategory.σ i).toOrderHom j.succ = j := by
  change i.predAbove j.succ = j
  exact Fin.predAbove_succ_of_le i j hij

theorem sigma_vertex_of_ge (i j : Fin (n + 1)) (hji : j ≤ i) :
    (SimplexCategory.σ i).toOrderHom j.castSucc = j := by
  change i.predAbove j.castSucc = j
  exact Fin.predAbove_castSucc_of_le i j hji

/-- Duplicating a vertex to the right of the original collapsed edge shifts
the prism vertex, retaining the original collapsed-edge index. -/
theorem map_sigma_of_le (i j : Fin (n + 1)) (hij : i ≤ j) :
    map (SimplexCategory.σ i) j.succ = SimplexCategory.σ i.castSucc := by
  ext r : 3
  by_cases hr : r ≤ j.succ.castSucc
  · have hlast : r ≠ Fin.last (n + 2) := by
      intro h
      subst r
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc, Fin.val_succ] at hr
      omega
    obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    rw [map_left _ _ _ (Fin.castSucc_le_castSucc_iff.mp hr)]
    change (i.predAbove r).castSucc = i.castSucc.predAbove r.castSucc
    exact (Fin.castSucc_predAbove_castSucc i r).symm
  · have hzero : r ≠ 0 := by intro h; subst r; simp at hr
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hzero
    have hjr : j.succ ≤ r := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hr ⊢
      omega
    rw [map_right _ _ _ hjr]
    have hir : i.castSucc < r := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hij hjr ⊢
      omega
    change (i.predAbove r).succ = i.castSucc.predAbove r.succ
    rw [Fin.predAbove_of_castSucc_lt i r hir,
      Fin.predAbove_succ_of_le i.castSucc r (le_of_lt hir), Fin.succ_pred]

/-- Duplicating a vertex to the left of the original collapsed edge shifts
the collapsed-edge index, retaining the original prism vertex. -/
theorem map_sigma_of_ge (i j : Fin (n + 1)) (hji : j ≤ i) :
    map (SimplexCategory.σ i) j.castSucc = SimplexCategory.σ i.succ := by
  ext r : 3
  by_cases hr : r ≤ j.castSucc.castSucc
  · have hlast : r ≠ Fin.last (n + 2) := by
      intro h
      subst r
      simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hr
      omega
    obtain ⟨r, rfl⟩ := Fin.eq_castSucc_of_ne_last hlast
    have hrj : r ≤ j.castSucc := Fin.castSucc_le_castSucc_iff.mp hr
    rw [map_left _ _ _ hrj]
    have hri : r ≤ i.castSucc := hrj.trans (Fin.castSucc_le_castSucc_iff.mpr hji)
    change (i.predAbove r).castSucc = i.succ.predAbove r.castSucc
    rw [Fin.predAbove_of_le_castSucc i r hri,
      Fin.predAbove_castSucc_of_le i.succ r (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hri ⊢
        omega), Fin.castSucc_castPred]
  · have hzero : r ≠ 0 := by intro h; subst r; simp at hr
    obtain ⟨r, rfl⟩ := Fin.eq_succ_of_ne_zero hzero
    have hjr : j.castSucc ≤ r := by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hr ⊢
      omega
    rw [map_right _ _ _ hjr]
    change (i.predAbove r).succ = i.succ.predAbove r.succ
    exact (Fin.succ_predAbove_succ i r).symm

end SimplexCategory.PrismMap

end
