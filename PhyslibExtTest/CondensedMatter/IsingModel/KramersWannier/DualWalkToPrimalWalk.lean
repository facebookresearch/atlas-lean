/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk`

* `kwc_pullback_eq_mapped_edges` on the empty walk at the origin;
* `kwc_primalWalkBoundsRegion_nil_case`: the empty walk bounds a region;
* the reductions `kwc_primalWalkBoundsRegion_of_leftRegionMatch` and
  `kwc_dualWalkBoundsRegion_of_primal` compose (both hypotheses are refuted downstream, in
  `FaceRegion` and `ShiftSquareCycle`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

-- The pullback of the empty walk is empty, matching the rotated empty walk.
example :
    Finset.image crossEdge.symm (SimpleGraph.Walk.nil :
        (hypercubicLattice 2).Walk (0 : Site 2) 0).edges.toFinset =
      (SimpleGraph.Walk.map rot90Iso.symm.toHom
        (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (0 : Site 2) 0)).edges.toFinset :=
  kwc_pullback_eq_mapped_edges _

-- The empty walk is the boundary-edge set of some set of sites.
example : ∃ S : Set (Site 2), ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
    (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (0 : Site 2) 0).edges.toFinset ↔
      bdEdge S s(u, v)) :=
  kwc_primalWalkBoundsRegion_nil_case

-- The two reductions compose.
example (h : kwc_PrimalWalkLeftRegionMatch) :
    Ising.DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge :=
  kwc_dualWalkBoundsRegion_of_primal (kwc_primalWalkBoundsRegion_of_leftRegionMatch h)

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk
