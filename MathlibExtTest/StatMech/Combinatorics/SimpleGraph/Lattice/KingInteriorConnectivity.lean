/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorConnectivity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingInteriorConnectivity`

* `mci_kingAdj` on small inputs and the bridge `mci_kingAdj_iff_kingAdj`.
* `mci_hyper_le_king`; the fjord is not 4-thin (`mci_fjord_not_fourThin`).
* `mci_FourThin` and `mci_KingRowLinked` hold for the staircase walk `ksd_stair` (from
  `KingSegmentDownCounterexample`), so the 4-thin hypothesis is satisfiable.
* `mci_offSupport_walk_interior` with the trivial walk at an interior site.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingInteriorConnectivity

example : mci_kingAdj (![0, 0] : Site 2) (![1, 1] : Site 2) ↔ KingAdj (![0, 0] : Site 2) ![1, 1] :=
  mci_kingAdj_iff_kingAdj _ _

example : hypercubicLattice 2 ≤ mci_kingGraph := mci_hyper_le_king

example : ¬ mci_FourThin sdc_fjord := mci_fjord_not_fourThin

example : mci_FourThin ksd_stair ∧ mci_KingRowLinked ksd_stair (![1, 1] : Site 2) :=
  ⟨ksd_stair_fourThin, ksd_kingRowLinked⟩

example : ∀ z ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk (![1, 1] : Site 2) _).support,
    z ∈ jil_offSupportInterior ksd_stair :=
  mci_offSupport_walk_interior ksd_stair _
    (fun z hz => by simp at hz; subst hz; exact ksd_off_11) ksd_mem_interior_11

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingInteriorConnectivity
