/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch`

* The ray count of the unit-cell loop: odd exactly on the unit cell, computed at two sites.
* `jsf_bdEdgeMatch_of_rayParity` instantiated at the unit cell (its parity hypotheses hold), and the
  star-hull identity `ndt_StarHull unitCell = unitCell`.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch

example : pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) :=
  jsf_bdEdgeMatch_of_rayParity _ jsf_unitCell_inside_odd jsf_unitCell_outside_even

example : jec_rayCount ![0, 0] (mpl_orbitLoop unitCell ucBase) = 1 := by
  rw [jsf_unitCell_rayCount]; simp

example : jec_rayCount ![3, 0] (mpl_orbitLoop unitCell ucBase) = 2 := by
  rw [jsf_unitCell_rayCount]; simp

example : ndt_StarHull unitCell = unitCell := jsf_starHull_unitCell_eq

example : unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := jsf_unitCell_eq_leftRegion

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RayParityBdEdgeMatch
