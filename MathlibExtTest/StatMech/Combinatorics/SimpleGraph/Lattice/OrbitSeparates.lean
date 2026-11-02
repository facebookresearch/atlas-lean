/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitSeparates
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitSeparates`

* `obs_orbitSeparates_singleton` and `obs_orbitCoversBoundaryEdges_singleton` for the boundary
  dart `e0` of `{0}`; `obs_orbitSeparates_of_coversBoundary` from the coverage.
* `obs_interfaceConnected_of_orbitSeparates` instantiated with the all-closed configuration, whose
  clusters are single sites: its hypothesis holds, so the theorem is nonvacuous.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitSeparates

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

/-- In the all-closed configuration the cluster of `o` is `{o}`. -/
theorem cluster_closed (o : Site 2) : cluster 2 (fun _ => false) o = {o} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | cons h _ => simp [openSubgraph_adj] at h
  · rintro rfl
    exact connected_refl _ _

example : OrbitSeparates ({(0 : Site 2)} : Set (Site 2)) e0 := obs_orbitSeparates_singleton 0 e0 e0_boundary

example : OrbitSeparates ({(0 : Site 2)} : Set (Site 2)) e0 :=
  obs_orbitSeparates_of_coversBoundary _ e0 e0_boundary
    (obs_orbitCoversBoundaryEdges_singleton 0 e0 e0_boundary)

example (o : Site 2) : InterfaceConnected (cluster 2 (fun _ => false) o) :=
  obs_interfaceConnected_of_orbitSeparates (ω := fun _ => false) o (fun e he => by
    rw [cluster_closed] at he ⊢
    exact obs_orbitSeparates_singleton o e he)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitSeparates
