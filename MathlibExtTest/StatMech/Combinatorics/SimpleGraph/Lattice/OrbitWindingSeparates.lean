/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates`

* For `K = {0}` and the boundary dart `e0`: the edge from the origin to `(1, 0)` is an orbit edge
  (`osp_singleton_posAxisEdge_isOrbitEdge`), it is a boundary edge of `K`
  (`osp_orbitEdge_bdEdge`), and `osp_singleton_orbitEdges_not_even_degree` (the orbit edges do not
  form an even-degree graph, so the orbit is not a closed lattice walk of its own edges).
* `osp_orbitWindsBdEdge_iff` unfolds `OrbitWindsBdEdge` for `{0}`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

example : IsOrbitEdge ({(0 : Site 2)} : Set (Site 2)) e0 0 (0 + ![1, 0]) :=
  osp_singleton_posAxisEdge_isOrbitEdge 0 e0 e0_boundary

example : bdEdge ({(0 : Site 2)} : Set (Site 2)) s(0, 0 + ![1, 0]) :=
  osp_orbitEdge_bdEdge _ e0 e0_boundary (osp_singleton_posAxisEdge_isOrbitEdge 0 e0 e0_boundary)

example : ∀ y : Site 2, IsOrbitEdge ({(0 : Site 2)} : Set (Site 2)) e0 (0 + ![1, 0]) y → y = 0 :=
  (osp_singleton_orbitEdges_not_even_degree 0 e0 e0_boundary).2

example : OrbitWindsBdEdge {(0 : Site 2)} (Set.finite_singleton _) e0 e0_boundary ↔
    (e0.tail ∈ osp_windingRegion {(0 : Site 2)} (Set.finite_singleton _) e0 e0_boundary ↔
      e0.head ∉ osp_windingRegion {(0 : Site 2)} (Set.finite_singleton _) e0 e0_boundary) :=
  osp_orbitWindsBdEdge_iff _ _ e0 e0_boundary

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates
