/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice




def faceCorner00 (a b : ℤ) : Site 2 := ![a, b]


def faceCorner10 (a b : ℤ) : Site 2 := ![a + 1, b]


def faceCorner11 (a b : ℤ) : Site 2 := ![a + 1, b + 1]


def faceCorner01 (a b : ℤ) : Site 2 := ![a, b + 1]


theorem faceAdj_bottom (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner00 a b) (faceCorner10 a b) := by
  simp [faceCorner00, faceCorner10, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_right (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner10 a b) (faceCorner11 a b) := by
  simp [faceCorner10, faceCorner11, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_top (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner11 a b) (faceCorner01 a b) := by
  simp [faceCorner11, faceCorner01, hypercubicLattice_adj, Fin.sum_univ_two]


theorem faceAdj_left (a b : ℤ) :
    (hypercubicLattice 2).Adj (faceCorner01 a b) (faceCorner00 a b) := by
  simp [faceCorner01, faceCorner00, hypercubicLattice_adj, Fin.sum_univ_two]





noncomputable def bdInd (S : Set (Site 2)) (x y : Site 2) : ℕ := by
  classical exact if (x ∈ S ↔ y ∉ S) then 1 else 0


theorem bdInd_comm (S : Set (Site 2)) (x y : Site 2) : bdInd S x y = bdInd S y x := by
  classical
  unfold bdInd
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp_all


theorem bdInd_eq_one_iff (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) :
    bdInd S x y = 1 ↔ (x, y) ∈ edgeBoundary 2 S := by
  classical
  unfold bdInd
  simp only [mem_edgeBoundary, hadj, true_and]
  by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]



noncomputable def faceBoundaryDegree (S : Set (Site 2)) (a b : ℤ) : ℕ :=
  bdInd S (faceCorner00 a b) (faceCorner10 a b)
    + bdInd S (faceCorner10 a b) (faceCorner11 a b)
    + bdInd S (faceCorner11 a b) (faceCorner01 a b)
    + bdInd S (faceCorner01 a b) (faceCorner00 a b)






theorem faceBoundaryDegree_even (S : Set (Site 2)) (a b : ℤ) :
    faceBoundaryDegree S a b % 2 = 0 := by
  classical
  unfold faceBoundaryDegree bdInd
  simp only [faceCorner00, faceCorner10, faceCorner11, faceCorner01]
  by_cases h0 : (![a, b] : Site 2) ∈ S <;>
    by_cases h1 : (![a + 1, b] : Site 2) ∈ S <;>
    by_cases h2 : (![a + 1, b + 1] : Site 2) ∈ S <;>
    by_cases h3 : (![a, b + 1] : Site 2) ∈ S <;>
    simp_all



theorem faceBoundaryDegree_le_four (S : Set (Site 2)) (a b : ℤ) :
    faceBoundaryDegree S a b ≤ 4 := by
  classical
  unfold faceBoundaryDegree bdInd
  have h₁ : ∀ x y : Site 2, (if (x ∈ S ↔ y ∉ S) then 1 else 0) ≤ 1 := by
    intro x y; by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]
  have := h₁ (faceCorner00 a b) (faceCorner10 a b)
  have := h₁ (faceCorner10 a b) (faceCorner11 a b)
  have := h₁ (faceCorner11 a b) (faceCorner01 a b)
  have := h₁ (faceCorner01 a b) (faceCorner00 a b)
  simp only [faceCorner00, faceCorner10, faceCorner11, faceCorner01] at *
  omega






theorem isClosed_iff_dualEdge_isOpen
    (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    ω e = false ↔ dualConfig ω (crossEdge e) = true := by
  rw [dual_isOpen_iff_isClosed, Equiv.symm_apply_apply]







theorem dualBoundaryDegree_even (S : Set (Site 2)) (a b : ℤ) :
    faceBoundaryDegree S a b % 2 = 0 := faceBoundaryDegree_even S a b




theorem crossEdge_bottom (a b : ℤ) :
    crossEdge s(faceCorner00 a b, faceCorner10 a b)
      = s(![-b, a], ![-b, a + 1]) := by
  simp [faceCorner00, faceCorner10, crossEdge_mk, rot90Fun]



theorem crossEdge_left (a b : ℤ) :
    crossEdge s(faceCorner01 a b, faceCorner00 a b)
      = s(![-(b + 1), a], ![-b, a]) := by
  simp [faceCorner01, faceCorner00, crossEdge_mk, rot90Fun]






theorem walk_mem_edgeBoundary (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ u v, (u, v) ∈ edgeBoundary 2 S := by
  classical
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab _p ih =>
    by_cases hb : b ∈ S
    · exact ih hb hy
    · exact ⟨a, b, hab, by simp [hx, hb]⟩





theorem edgeBoundary_nonempty_of_walk (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    (edgeBoundary 2 S).Nonempty := by
  obtain ⟨u, v, huv⟩ := walk_mem_edgeBoundary S w hx hy
  exact ⟨(u, v), huv⟩



variable {ω : ConfigSpace (Sym2 (Site 2))}




theorem edge_leaving_cluster_isClosed (o : Site 2) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y)
    (hx : x ∈ cluster 2 ω o) (hy : y ∉ cluster 2 ω o) :
    ω s(x, y) = false := by
  by_contra h
  exact hy (hx.trans (IsOpenEdge.connected ⟨hadj, by simpa using h⟩))






theorem cluster_edgeBoundary_isClosed (o : Site 2) {x y : Site 2}
    (h : (x, y) ∈ edgeBoundary 2 (cluster 2 ω o)) :
    ω s(x, y) = false := by
  classical
  obtain ⟨hadj, hsep⟩ := h
  by_cases hx : x ∈ cluster 2 ω o
  · exact edge_leaving_cluster_isClosed o hadj hx (hsep.mp hx)
  · 
    have hy : y ∈ cluster 2 ω o := by
      by_contra hy; exact hx (hsep.mpr hy)
    have := edge_leaving_cluster_isClosed o hadj.symm hy (by simpa using hx)
    rwa [Sym2.eq_swap]







theorem cluster_edgeBoundary_crosses_dual_open (o : Site 2) {x y : Site 2}
    (h : (x, y) ∈ edgeBoundary 2 (cluster 2 ω o)) :
    dualConfig ω (crossEdge s(x, y)) = true :=
  (isClosed_iff_dualEdge_isOpen ω s(x, y)).mp (cluster_edgeBoundary_isClosed o h)

end Lattice

end StatMech
