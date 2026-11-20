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
import Code.Lattice.JordanZ2
import Code.Lattice.PlanarTopology
import Code.Lattice.JordanEnclosure

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice











noncomputable def crossCount (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ := by
  classical
  exact w.edges.countP (fun e => decide (bdEdge S e))

@[simp] theorem crossCount_nil (S : Set (Site 2)) (x : Site 2) :
    crossCount S (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical
  simp [crossCount]

open Classical in

theorem crossCount_cons (S : Set (Site 2)) {a b c : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) (p : (hypercubicLattice 2).Walk b c) :
    crossCount S (Walk.cons hab p) =
      (if bdEdge S s(a, b) then 1 else 0) + crossCount S p := by
  rw [crossCount, crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
  by_cases h : bdEdge S s(a, b)
  · rw [if_pos h, if_pos (by simp [h])]; ring
  · rw [if_neg h, if_neg (by simp [h])]; ring



theorem crossCount_append (S : Set (Site 2)) {x y z : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y z) :
    crossCount S (p.append q) = crossCount S p + crossCount S q := by
  classical
  rw [crossCount, crossCount, crossCount, SimpleGraph.Walk.edges_append, List.countP_append]




theorem crossCount_reverse (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    crossCount S w.reverse = crossCount S w := by
  classical
  rw [crossCount, crossCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]











theorem crossCount_parity (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  induction w with
  | nil => simp [crossCount]
  | @cons a b c hab p ih =>
    rw [crossCount, SimpleGraph.Walk.edges_cons, List.countP_cons]
    rw [crossCount] at ih
    by_cases hbd : bdEdge S s(a, b)
    · rw [if_pos (by simp [hbd]), Nat.even_add_one, ih]
      rw [bdEdge_mk] at hbd
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;> simp_all
    · rw [if_neg (by simp [hbd]), add_zero, ih]
      rw [bdEdge_mk] at hbd
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> by_cases hc : c ∈ S <;> simp_all







theorem crossCount_parity_eq_of_sameEndpoints (S : Set (Site 2)) {x y : Site 2}
    (w₁ w₂ : (hypercubicLattice 2).Walk x y) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
  classical
  have h1 := crossCount_parity S w₁
  have h2 := crossCount_parity S w₂
  rw [Nat.even_iff] at h1 h2
  by_cases hP : (x ∈ S ↔ y ∈ S)
  · rw [h1.mpr hP, h2.mpr hP]
  · have e1 : crossCount S w₁ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (crossCount S w₁) with h | h
      · exact absurd (h1.mp h) hP
      · exact h
    have e2 : crossCount S w₂ % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (crossCount S w₂) with h | h
      · exact absurd (h2.mp h) hP
      · exact h
    rw [e1, e2]








theorem face_flip_parity (S : Set (Site 2)) (a b : ℤ)
    (w₁ w₂ : (hypercubicLattice 2).Walk (faceCorner00 a b) (faceCorner11 a b)) :
    crossCount S w₁ % 2 = crossCount S w₂ % 2 :=
  crossCount_parity_eq_of_sameEndpoints S w₁ w₂




theorem crossCount_even_of_loop (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  (crossCount_parity S w).mpr Iff.rfl






theorem crossCount_odd_of_separated (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) := by
  rw [crossCount_parity]
  intro h
  exact hy (h.mp hx)











noncomputable def latticeMinusBarrier (S : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ ¬ bdEdge S s(x, y)
  symm := by
    intro x y ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [Sym2.eq_swap]
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem latticeMinusBarrier_adj (S : Set (Site 2)) (x y : Site 2) :
    (latticeMinusBarrier S).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ ¬ bdEdge S s(x, y) := Iff.rfl


theorem latticeMinusBarrier_le (S : Set (Site 2)) :
    latticeMinusBarrier S ≤ hypercubicLattice 2 := fun _ _ h => h.1





theorem latticeMinusBarrier_sameSide (S : Set (Site 2)) {x y : Site 2}
    (w : (latticeMinusBarrier S).Walk x y) : (x ∈ S ↔ y ∈ S) := by
  classical
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    have hnb : ¬ bdEdge S s(a, b) := hab.2
    rw [bdEdge_mk] at hnb
    have hab_side : (a ∈ S ↔ b ∈ S) := by
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp_all
    exact hab_side.trans ih






theorem not_reachable_latticeMinusBarrier (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (latticeMinusBarrier S).Reachable x y := by
  rintro ⟨w⟩
  exact hy ((latticeMinusBarrier_sameSide S w).mp hx)










theorem faceBoundaryGraph_sharedPrimalEdge_bdEdge (S : Set (Site 2)) {f g : Site 2}
    (h : (faceBoundaryGraph S).Adj f g) : bdEdge S (sharedPrimalEdge f g) := h.2




theorem sharedPrimalEdge_isLatticeEdge {f g : Site 2}
    (_h : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q := by
  classical
  unfold sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0]
    exact ⟨_, _, rfl, by simp [hypercubicLattice_adj, Fin.sum_univ_two]⟩
  · rw [if_neg h0]
    exact ⟨_, _, rfl, by simp [hypercubicLattice_adj, Fin.sum_univ_two]⟩




theorem faceBoundaryWalk_edges_bdEdge (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) {f g : Site 2} (h : s(f, g) ∈ c.edges) :
    bdEdge S (sharedPrimalEdge f g) := by
  have hadj : (faceBoundaryGraph S).Adj f g := c.adj_of_mem_edges h
  exact faceBoundaryGraph_sharedPrimalEdge_bdEdge S hadj







variable {ω : ConfigSpace (Sym2 (Site 2))}






theorem cluster_separated_from_exterior (o : Site 2) {z : Site 2}
    (hz : z ∉ cluster 2 ω o) :
    ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z :=
  not_reachable_latticeMinusBarrier (cluster 2 ω o) (self_mem_cluster ω o) hz






theorem origin_crossCount_odd (o : Site 2) {z : Site 2}
    (hz : z ∉ cluster 2 ω o) (w : (hypercubicLattice 2).Walk o z) :
    ¬ Even (crossCount (cluster 2 ω o) w) :=
  crossCount_odd_of_separated (cluster 2 ω o) (self_mem_cluster ω o) hz w















theorem cluster_enclosed_by_dualCircuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z := by
  refine ⟨exists_dualCircuit_of_finite_cluster o hfin w hz,
    cluster_separated_from_exterior o hz⟩






theorem cluster_enclosed_with_winding (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z ∧
      ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
  refine ⟨exists_dualCircuit_of_finite_cluster o hfin w hz,
    cluster_separated_from_exterior o hz, fun γ => origin_crossCount_odd o hz γ⟩

end Lattice

end StatMech
