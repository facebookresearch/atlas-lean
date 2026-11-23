/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.PeierlsContourCount

/-!
# A connected cluster is determined by its edge boundary

A finite connected set of sites containing the origin is recovered from its set of boundary
edges.

## i. Overview

For a set of sites `K ⊆ ℤ^d`, an edge of the hypercubic lattice *straddles* `K` if exactly one
endpoint lies in `K`; these edges form the edge boundary `∂K`. Deleting `∂K` from the lattice
leaves a graph in which no walk crosses between `K` and its complement, while every walk inside
`K` survives. Hence a connected cluster containing the origin is exactly the connected component
of the origin in the lattice with `∂K` removed, and the map `K ↦ ∂K` is injective on such
clusters. This injectivity is the first step of the Peierls contour count.

## ii. Key results

- `boundaryEdgeSet` : the edge boundary `∂K`.
- `connectedCluster_eq_component` : `K` is the component of the origin in the lattice minus `∂K`.
- `boundaryEdgeSet_injective` : `K ↦ ∂K` is injective on connected clusters.

## iii. Table of contents

- A. Straddling edges and the edge boundary
- B. Walks avoiding the boundary
- C. Recovery of the cluster

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin)

variable {d : ℕ}

/-! ## A. Straddling edges and the edge boundary -/

/-- An edge straddles `K` if exactly one of its endpoints lies in `K`. -/
def edgeStraddles (K : Set (Site d)) (e : Sym2 (Site d)) : Prop := by
  classical
  exact Sym2.lift ⟨fun x y => (x ∈ K ↔ y ∉ K), by
    intro x y
    simp only [eq_iff_iff]
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto⟩ e

@[simp] lemma edgeStraddles_mk (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := Iff.rfl

lemma edgeStraddles_comm (K : Set (Site d)) (x y : Site d) :
    edgeStraddles K s(x, y) ↔ edgeStraddles K s(y, x) := by
  rw [edgeStraddles_mk, edgeStraddles_mk]
  classical
  by_cases hx : x ∈ K <;> by_cases hy : y ∈ K <;> tauto

/-- The edge boundary `∂K`: the lattice edges that straddle `K`. -/
def boundaryEdgeSet (K : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | e ∈ (hypercubicLattice d).edgeSet ∧ edgeStraddles K e}

/-- The hypercubic lattice with the edges straddling `K` removed. -/
def latticeMinusBoundary (K : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y)
  symm := by
    refine ⟨?_⟩
    intro x y ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [← edgeStraddles_comm]
  loopless := ⟨fun x h => (hypercubicLattice d).irrefl h.1⟩

@[simp] lemma latticeMinusBoundary_adj (K : Set (Site d)) (x y : Site d) :
    (latticeMinusBoundary K).Adj x y ↔
      (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y) := Iff.rfl

lemma latticeMinusBoundary_le (K : Set (Site d)) :
    latticeMinusBoundary K ≤ hypercubicLattice d := fun _ _ h => h.1

/-! ## B. Walks avoiding the boundary -/

lemma barrier_sameComponent (K : Set (Site d)) {x y : Site d}
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

lemma not_reachable_in_barrier_of_separated (K : Set (Site d)) {x y : Site d}
    (hx : x ∈ K) (hy : y ∉ K) : ¬ (latticeMinusBoundary K).Reachable x y := by
  rintro ⟨w⟩
  exact hy ((barrier_sameComponent K w).mp hx)

lemma latticeOn_le_latticeMinusBoundary (K : Set (Site d)) :
    latticeOn K ≤ latticeMinusBoundary K := by
  intro x y h
  obtain ⟨hadj, hx, hy⟩ := h
  refine ⟨hadj, ?_⟩
  rw [edgeStraddles_mk]
  simp only [hx, hy, iff_false, not_true]
  exact fun h => h

lemma reachable_in_barrier_of_latticeOn (K : Set (Site d)) {x y : Site d}
    (h : (latticeOn K).Reachable x y) : (latticeMinusBoundary K).Reachable x y :=
  h.mono (latticeOn_le_latticeMinusBoundary K)

lemma reachable_in_barrier_of_mem {K : Finset (Site d)} (hK : IsConnectedCluster K)
    {x : Site d} (hx : x ∈ K) :
    (latticeMinusBoundary (↑K : Set (Site d))).Reachable (origin d) x :=
  reachable_in_barrier_of_latticeOn _ (hK.2 x hx)

/-! ## C. Recovery of the cluster -/

lemma connectedCluster_eq_component {K : Finset (Site d)} (hK : IsConnectedCluster K)
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

lemma edgeStraddles_iff_mem_boundaryEdgeSet (K : Set (Site d)) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) :
    edgeStraddles K s(x, y) ↔ s(x, y) ∈ boundaryEdgeSet K := by
  unfold boundaryEdgeSet
  rw [Set.mem_ofPred_eq, SimpleGraph.mem_edgeSet]
  refine ⟨fun h => ⟨hadj, h⟩, fun h => h.2⟩

lemma latticeMinusBoundary_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Set (Site d)}
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

lemma connCluster_eq_of_boundaryEdgeSet_eq {K₁ K₂ : Finset (Site d)}
    (hK₁ : IsConnectedCluster K₁) (hK₂ : IsConnectedCluster K₂)
    (h : boundaryEdgeSet (↑K₁ : Set (Site d)) = boundaryEdgeSet (↑K₂ : Set (Site d))) :
    K₁ = K₂ := by
  have hbarrier : latticeMinusBoundary (↑K₁ : Set (Site d))
      = latticeMinusBoundary (↑K₂ : Set (Site d)) :=
    latticeMinusBoundary_eq_of_boundaryEdgeSet_eq h
  apply Finset.coe_injective
  ext x
  rw [connectedCluster_eq_component hK₁ x, connectedCluster_eq_component hK₂ x, hbarrier]

lemma boundaryEdgeSet_injective :
    Set.InjOn (fun K : Finset (Site d) => boundaryEdgeSet (↑K : Set (Site d)))
      {K | IsConnectedCluster K} := by
  intro K₁ hK₁ K₂ hK₂ h
  exact connCluster_eq_of_boundaryEdgeSet_eq hK₁ hK₂ h

end Lattice

end StatMech
