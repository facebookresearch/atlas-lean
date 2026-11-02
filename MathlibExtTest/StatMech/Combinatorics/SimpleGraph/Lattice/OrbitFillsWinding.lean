/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding`

* `ofw_orbitFillsWinding_iff_via_coverage` for `K = {0}` and the boundary dart `e0`; the coverage
  hypothesis is supplied by `obs_orbitCoversBoundaryEdges_singleton`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

example : OrbitFillsWinding {(0 : Site 2)} (Set.finite_singleton _) e0 e0_boundary ↔
    OrbitWindingRevMatch {(0 : Site 2)} (Set.finite_singleton _) e0 e0_boundary :=
  ofw_orbitFillsWinding_iff_via_coverage _ _ e0 e0_boundary
    (obs_orbitCoversBoundaryEdges_singleton 0 e0 e0_boundary)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitFillsWinding
