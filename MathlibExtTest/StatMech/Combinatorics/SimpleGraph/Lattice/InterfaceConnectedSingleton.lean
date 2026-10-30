/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton`

* `ifc_interfaceConnected`: a single site is `InterfaceConnected`.
* `ifc_singleton_sameOrbit` for the boundary dart `e0` from the origin to `(1, 0)`.
* `ifc_unit_four_cases` and `unitWt` at `(1, 0)`; `facingDart` has the prescribed head.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton

/-- The dart from the origin to `(1, 0)`. -/
noncomputable def e0 : Dart := mkDart 0 ![1, 0] (by decide)

theorem e0_boundary : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e0 := by
  refine ⟨by simp [e0], ?_⟩
  simp only [e0, mkDart_head, zero_add, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp at this

example : InterfaceConnected ({(0 : Site 2)} : Set (Site 2)) := ifc_interfaceConnected 0

example : SameOrbit ({(0 : Site 2)} : Set (Site 2)) e0 e0 :=
  ifc_singleton_sameOrbit 0 e0 e0 e0_boundary e0_boundary

example : unitWt (![1, 0] : Site 2) = 1 := by decide

example (g : Site 2) (hg : unitWt g = 1) :
    g = ![1, 0] ∨ g = ![-1, 0] ∨ g = ![0, 1] ∨ g = ![0, -1] := ifc_unit_four_cases g hg

example (v : Site 2) : (facingDart v ![1, 0] (by decide)).head = v := by
  simp only [facingDart, mkDart_head, sub_add_cancel]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton
