/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplexCategory.PrismMap

/-!
# Degeneracy formulas for duplicated-vertex simplex maps

The elementary degeneracy σ_i : [n+1] → [n] collapses vertices i and i+1. For i ≤ j it sends
j+1 to j, while for j ≤ i it sends j to j.

Its prism lift at the source vertex j+1, with i ≤ j, is the elementary degeneracy with the
same collapsed-edge index i in the enlarged ordinals. Its lift at the source vertex j, with j
≤ i, is the elementary degeneracy with index i+1. These two formulas give the two degeneracy
cases for prism operators, including the equality cases.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SimplexCategory.PrismMap

variable {n : ℕ}

/-- Degeneracy value on a vertex to the right of its collapsed edge.

For i,j ∈ Fin(n+1) with i ≤ j, the map σ_i : [n+1] → [n] sends j.succ to j. -/
theorem sigma_vertex_of_le (i j : Fin (n + 1)) (hij : i ≤ j) :
    (SimplexCategory.σ i).toOrderHom j.succ = j := by
  change i.predAbove j.succ = j
  exact Fin.predAbove_succ_of_le i j hij

/-- Degeneracy value on a vertex to the left of its collapsed edge.

For i,j ∈ Fin(n+1) with j ≤ i, the map σ_i : [n+1] → [n] sends j.castSucc to j. -/
theorem sigma_vertex_of_ge (i j : Fin (n + 1)) (hji : j ≤ i) :
    (SimplexCategory.σ i).toOrderHom j.castSucc = j := by
  change i.predAbove j.castSucc = j
  exact Fin.predAbove_castSucc_of_le i j hji

/-- Prism lift of a degeneracy at a right-hand duplicated vertex.

For i ≤ j, the prism map Φ(σ_i,j.succ) : [n+2] → [n+1] is σ_{i.castSucc}. The duplicated
vertex lies to the right of the collapsed edge, so the edge retains index i. -/
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

/-- Prism lift of a degeneracy at a left-hand duplicated vertex.

For j ≤ i, the prism map Φ(σ_i,j.castSucc) : [n+2] → [n+1] is σ_{i.succ}. Duplicating on this
side shifts the collapsed-edge index from i to i+1. -/
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
