/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Grounded weighted Laplacian checks

Focused checks for `MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian`:

- a three-node path `0 → 1 → 2` with weights `1` and `2` plus a zero-weight
  chord `0 → 2`, grounded at `0`: positive definite and invertible, and the
  constant vector spans the kernel of the full Laplacian;
- the same nodes with only the arc `0 → 1`: node `2` is isolated, the grounded
  matrix is not positive definite, so the reachability hypothesis fails;
- one arc `0 → 1` of weight zero: not positive definite, so zero-weight arcs
  cannot supply connectivity.

These are elaboration and non-vacuity checks, not new results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MathlibExtTest.Combinatorics.Graph.ArcNetworkLaplacian

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
  MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian

/-- Deleting a ground node `r` where `x r = 0` commutes with `mulVec`. -/
theorem submatrix_mulVec_of_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (r : V) (x : V → ℝ) (hx : x r = 0) (i : {v // v ≠ r}) :
    (M.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val *ᵥ fun j : {v // v ≠ r} => x j.1) i =
      (M *ᵥ x) i.1 := by
  simp only [mulVec, dotProduct, submatrix_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r, hx, mul_zero, zero_add]

/-- A grounded matrix with a nonzero kernel vector vanishing at the ground is
not positive definite. -/
theorem not_posDef_of_mulVec_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (r : V) (x : V → ℝ) (hx : x r = 0) (hM : M *ᵥ x = 0)
    (j : {v // v ≠ r}) (hj : x j.1 ≠ 0) :
    ¬ (M.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val).PosDef := by
  intro h
  have hy : (fun i : {v // v ≠ r} => x i.1) ≠ 0 := fun h0 => hj (congrFun h0 j)
  have hpos := h.dotProduct_mulVec_pos hy
  have hzero : (M.submatrix (Subtype.val : {v // v ≠ r} → V) Subtype.val *ᵥ
      fun i : {v // v ≠ r} => x i.1) = 0 := by
    funext i
    rw [submatrix_mulVec_of_eq_zero M r x hx i, hM, Pi.zero_apply, Pi.zero_apply]
  rw [hzero, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

/-! ### Connected path with a zero-weight chord -/

def tail3 : Fin 3 → Fin 3 := ![0, 1, 0]
def head3 : Fin 3 → Fin 3 := ![1, 2, 2]
def w3 : Fin 3 → ℝ := ![1, 2, 0]

theorem w3_nonneg : ∀ e, 0 ≤ w3 e := by
  intro e
  fin_cases e <;> norm_num [w3]

theorem reachable3 : ∀ v, (positiveArcGraph tail3 head3 w3).Reachable 0 v := by
  have h01 : (positiveArcGraph tail3 head3 w3).Adj 0 1 :=
    (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by decide, Or.inl ⟨0, by norm_num [w3], rfl, rfl⟩⟩
  have h12 : (positiveArcGraph tail3 head3 w3).Adj 1 2 :=
    (SimpleGraph.fromRel_adj _ _ _).mpr ⟨by decide, Or.inl ⟨1, by norm_num [w3], rfl, rfl⟩⟩
  intro v
  fin_cases v
  · rfl
  · exact h01.reachable
  · exact h01.reachable.trans h12.reachable

/-- The grounded path Laplacian is positive definite. -/
example :
    ((incidenceMatrix tail3 head3 * diagonal w3 * (incidenceMatrix tail3 head3)ᵀ).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).PosDef :=
  grounded_weightedLaplacian_posDef tail3 head3 w3 w3_nonneg 0 reachable3

/-- The grounded path Laplacian is invertible. -/
example :
    IsUnit ((incidenceMatrix tail3 head3 * diagonal w3 * (incidenceMatrix tail3 head3)ᵀ).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3)) :=
  grounded_weightedLaplacian_isUnit tail3 head3 w3 w3_nonneg 0 reachable3

/-- The kernel of the full path Laplacian is the constant vectors. -/
example (x : Fin 3 → ℝ) :
    (incidenceMatrix tail3 head3 * diagonal w3 * (incidenceMatrix tail3 head3)ᵀ) *ᵥ x = 0 ↔
      ∀ v, x v = x 0 :=
  weightedLaplacian_mulVec_eq_zero_iff_of_reachable tail3 head3 w3 w3_nonneg 0 reachable3 x

/-- The energy of the potential `(0, 1, 3)` is `1 * 1 ^ 2 + 2 * 2 ^ 2 + 0 * 3 ^ 2 = 9`. -/
example :
    ![0, 1, 3] ⬝ᵥ
      ((incidenceMatrix tail3 head3 * diagonal w3 * (incidenceMatrix tail3 head3)ᵀ) *ᵥ
        ![(0 : ℝ), 1, 3]) = 9 := by
  rw [dotProduct_weightedLaplacian_mulVec]
  simp [Fin.sum_univ_three, tail3, head3, w3]
  norm_num

/-! ### Disconnected network: node `2` is isolated -/

def tail1 : Fin 1 → Fin 3 := ![0]
def head1 : Fin 1 → Fin 3 := ![1]

/-- The indicator of node `2` is a kernel vector of the full Laplacian. -/
theorem isolated_mulVec_eq_zero (w : Fin 1 → ℝ) :
    (incidenceMatrix tail1 head1 * diagonal w * (incidenceMatrix tail1 head1)ᵀ) *ᵥ
      (Pi.single 2 1 : Fin 3 → ℝ) = 0 := by
  have hflow : (incidenceMatrix tail1 head1)ᵀ *ᵥ (Pi.single 2 1 : Fin 3 → ℝ) = 0 := by
    funext e
    rw [incidenceMatrix_transpose_mulVec_apply]
    fin_cases e
    simp [tail1, head1]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hflow, mulVec_zero, mulVec_zero]

/-- Negative case: with node `2` isolated, the grounded matrix is not positive
definite. -/
theorem disconnected_not_posDef :
    ¬ ((incidenceMatrix tail1 head1 * diagonal (fun _ => (1 : ℝ)) *
        (incidenceMatrix tail1 head1)ᵀ).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).PosDef :=
  not_posDef_of_mulVec_eq_zero _ 0 _ (by simp) (isolated_mulVec_eq_zero _)
    ⟨2, by decide⟩ (by simp)

/-- The failing hypothesis is exactly the reachability of every node from the
ground: positive weights do not rescue a disconnected network. -/
example : ¬ ∀ v, (positiveArcGraph tail1 head1 (fun _ => (1 : ℝ))).Reachable 0 v :=
  fun h => disconnected_not_posDef
    (grounded_weightedLaplacian_posDef tail1 head1 _ (fun _ => zero_le_one) 0 h)

/-! ### A zero-weight arc does not connect -/

def tail01 : Fin 1 → Fin 2 := ![0]
def head01 : Fin 1 → Fin 2 := ![1]

/-- Negative case: a single arc `0 → 1` of weight zero leaves the grounded
matrix not positive definite. -/
example :
    ¬ ((incidenceMatrix tail01 head01 * diagonal (fun _ => (0 : ℝ)) *
        (incidenceMatrix tail01 head01)ᵀ).submatrix
      (Subtype.val : {v : Fin 2 // v ≠ 0} → Fin 2) Subtype.val).PosDef := by
  refine not_posDef_of_mulVec_eq_zero _ 0 (Pi.single 1 1) (by simp) ?_ ⟨1, by decide⟩ (by simp)
  rw [diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, zero_mulVec]

/-- At strictly positive weights the weighted arc graph is
the constant-weight underlying graph; at weight zero it is
not (the arc above gives no adjacency). -/
example : positiveArcGraph tail01 head01 (fun _ => (2 : ℝ))
    = positiveArcGraph tail01 head01 (fun _ => (1 : ℝ)) :=
  positiveArcGraph_eq_of_pos tail01 head01 (fun _ => by norm_num)

example : ¬ (positiveArcGraph tail01 head01 (fun _ => (0 : ℝ))).Adj 0 1 := by
  rw [positiveArcGraph, SimpleGraph.fromRel_adj]
  rintro ⟨-, ⟨e, he, -, -⟩ | ⟨e, he, -, -⟩⟩ <;> simp at he

#print axioms
  MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.positiveArcGraph_eq_of_pos

end MathlibExtTest.Combinatorics.Graph.ArcNetworkLaplacian
