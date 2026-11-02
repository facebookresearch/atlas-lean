/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected`

* `ifg_boundaryKingConnected_of_clusterConnected` for `K = {0}` (using `ifc_interfaceConnected`)
  and the boundary dart `e0`.
* The refutation `ifg_not_orbitKingTransport_of_finite` for the two-site set `{0, (1, 0)}`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

example : SameOrbit ({(0 : Site 2)} : Set (Site 2)) e0 e0 ∧
    (boundaryKingGraph ({(0 : Site 2)} : Set (Site 2))).Reachable
      ⟨e0.head, e0_boundary.2⟩ ⟨e0.head, e0_boundary.2⟩ :=
  ifg_boundaryKingConnected_of_clusterConnected _ (ifc_interfaceConnected 0) e0_boundary
    e0_boundary (Reachable.refl _)

example : ¬ OrbitKingTransport ({0, ![1, 0]} : Set (Site 2)) :=
  ifg_not_orbitKingTransport_of_finite _ (Set.toFinite _) (Set.insert_nonempty _ _)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected
