/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialSurjectivity
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.FacialSurjectivity`

* `fsv_RegionSingleFace_singleton`, and `fsv_boundaryDartSet_eq_orbit` for `{0}` and the boundary
  dart `e0` (all boundary darts of a site form one orbit, `ifc_singleton_sameOrbit`).
* `fsv_componentCount_eq_canonicalCount` for the one-vertex closed walk at the origin.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FacialSurjectivity

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

example : fsv_RegionSingleFace ({(0 : Site 2)} : Set (Site 2)) := fsv_RegionSingleFace_singleton 0

example : {d : Dart | IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) d} =
    {d : Dart | SameOrbit ({(0 : Site 2)} : Set (Site 2)) e0 d} :=
  fsv_boundaryDartSet_eq_orbit _ e0_boundary fun d hd =>
    ifc_singleton_sameOrbit 0 e0 d e0_boundary hd

/-- The one-vertex closed walk at the origin. -/
abbrev W0 : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] := Walk.nil

example : Nat.card (fcb_offComplGraph W0).ConnectedComponent =
    Nat.card (fsv_canonicalFamily W0) := fsv_componentCount_eq_canonicalCount W0

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.FacialSurjectivity
