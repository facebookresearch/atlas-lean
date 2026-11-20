/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarTopology
import Code.Ising.PeierlsContourCount

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin)

variable {d : ℕ}














def edgeStraddles (K : Set (Site d)) (e : Sym2 (Site d)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y => (x ∈ K ↔ y ∉ K), by
    intro x y
    simp only [eq_iff_iff]
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto⟩ e

@[simp] theorem edgeStraddles_mk (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := Iff.rfl

theorem edgeStraddles_comm (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ edgeStraddles K s(y, x) := by
  rw [edgeStraddles_mk, edgeStraddles_mk]
  classical
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto




def boundaryEdgeSet (K : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | e ∈ (hypercubicLattice d).edgeSet ∧ edgeStraddles K e}



def latticeMinusBoundary (K : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y)
  symm := by
    intro x y ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [← edgeStraddles_comm]
  loopless := ⟨fun x h => (hypercubicLattice d).irrefl h.1⟩

@[simp] theorem latticeMinusBoundary_adj (K : Set (Site d)) (x y : Site d) :
    (latticeMinusBoundary K).Adj x y ↔
      (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y) := Iff.rfl

theorem latticeMinusBoundary_le (K : Set (Site d)) :
    latticeMinusBoundary K ≤ hypercubicLattice d := fun _ _ h => h.1












theorem barrier_sameComponent (K : Set (Site d)) {x y : Site d}
    (w : (latticeMinusBoundary K).Walk x y) : (x ∈ K ↔ y ∈ K) := by
  classical
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    have hnb : ¬ edgeStraddles K s(a, b) := hab.2
    rw [edgeStraddles_mk] at hnb
    have hab_side : (a ∈ K ↔ b ∈ K) := by
      by_cases ha : a ∈ K <;> by_cases hb : b ∈ K <;> simp_all
    exact hab_side.trans ih





theorem not_reachable_in_barrier_of_separated (K : Set (Site d)) {x y : Site d}
    (hx : x ∈ K) (hy : y ∉ K) : ¬ (latticeMinusBoundary K).Reachable x y := by
  rintro ⟨w⟩
  exact hy ((barrier_sameComponent K w).mp hx)










theorem latticeOn_le_latticeMinusBoundary (K : Set (Site d)) :
    latticeOn K ≤ latticeMinusBoundary K := by
  intro x y h
  obtain ⟨hadj, hx, hy⟩ := h
  refine ⟨hadj, ?_⟩
  rw [edgeStraddles_mk]
  
  simp only [hx, hy, iff_false, not_true]
  exact fun h => h



theorem reachable_in_barrier_of_latticeOn (K : Set (Site d)) {x y : Site d}
    (h : (latticeOn K).Reachable x y) : (latticeMinusBoundary K).Reachable x y :=
  h.mono (latticeOn_le_latticeMinusBoundary K)




theorem reachable_in_barrier_of_mem {K : Finset (Site d)} (hK : IsConnectedCluster K)
    {x : Site d} (hx : x ∈ K) :
    (latticeMinusBoundary (↑K : Set (Site d))).Reachable (origin d) x :=
  reachable_in_barrier_of_latticeOn _ (hK.2 x hx)







theorem connectedCluster_eq_component {K : Finset (Site d)} (hK : IsConnectedCluster K)
    (x : Site d) :
    x ∈ (↑K : Set (Site d)) ↔
      (latticeMinusBoundary (↑K : Set (Site d))).Reachable (origin d) x := by
  constructor
  · intro hx
    exact reachable_in_barrier_of_mem hK (by exact_mod_cast hx)
  · intro hx
    by_contra hxK
    exact not_reachable_in_barrier_of_separated (↑K : Set (Site d))
      (by exact_mod_cast hK.1) hxK hx













theorem edgeStraddles_iff_mem_boundaryEdgeSet (K : Set (Site d)) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) :
    edgeStraddles K s(x, y) ↔ s(x, y) ∈ boundaryEdgeSet K := by
  unfold boundaryEdgeSet
  rw [Set.mem_setOf_eq, SimpleGraph.mem_edgeSet]
  refine ⟨fun h => ⟨hadj, h⟩, fun h => h.2⟩



theorem latticeMinusBoundary_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Set (Site d)}
    (h : boundaryEdgeSet K₁ = boundaryEdgeSet K₂) :
    latticeMinusBoundary K₁ = latticeMinusBoundary K₂ := by
  ext x y
  rw [latticeMinusBoundary_adj, latticeMinusBoundary_adj]
  constructor
  · rintro ⟨hadj, hnb⟩
    refine ⟨hadj, ?_⟩
    rw [edgeStraddles_iff_mem_boundaryEdgeSet K₂ hadj, ← h,
      ← edgeStraddles_iff_mem_boundaryEdgeSet K₁ hadj]
    exact hnb
  · rintro ⟨hadj, hnb⟩
    refine ⟨hadj, ?_⟩
    rw [edgeStraddles_iff_mem_boundaryEdgeSet K₁ hadj, h,
      ← edgeStraddles_iff_mem_boundaryEdgeSet K₂ hadj]
    exact hnb




theorem connCluster_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Finset (Site d)}
    (hK₁ : IsConnectedCluster K₁) (hK₂ : IsConnectedCluster K₂)
    (h : boundaryEdgeSet (↑K₁ : Set (Site d)) = boundaryEdgeSet (↑K₂ : Set (Site d))) :
    K₁ = K₂ := by
  have hbarrier : latticeMinusBoundary (↑K₁ : Set (Site d))
      = latticeMinusBoundary (↑K₂ : Set (Site d)) :=
    latticeMinusBoundary_eq_of_boundaryEdgeSet_eq h
  apply Finset.coe_injective
  ext x
  rw [connectedCluster_eq_component hK₁ x, connectedCluster_eq_component hK₂ x, hbarrier]








theorem boundaryEdgeSet_injective :
    Set.InjOn (fun K : Finset (Site d) => boundaryEdgeSet (↑K : Set (Site d)))
      {K | IsConnectedCluster K} := by
  intro K₁ hK₁ K₂ hK₂ h
  exact connCluster_eq_of_boundaryEdgeSet_eq hK₁ hK₂ h

end Lattice

end StatMech
