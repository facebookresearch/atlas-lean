/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting`

* `mng_disjointRouting_of_mengerCore` and `mng_corridorCover_of_mengerCover` as conditional
  statements in `ℤ²`.
* `MengerRoutingCover` unfolds to a Menger core on every configuration of `threeMeetBox`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation
open _root_.StatMech.Percolation.DisjointPaths

-- A Menger core gives disjoint corridor routing.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : MengerCore ω) : DisjointCorridorRouting ω :=
  mng_disjointRouting_of_mengerCore ω h

-- The routing cover gives the corridor cover.
example (n : ℕ) (h : MengerRoutingCover 2 n) :
    threeMeetBox 2 n ⊆ ⋃ (a₁ : Site 2) (a₂ : Site 2) (a₃ : Site 2) (G : Finset (Sym2 (Site 2))),
      CorridorWorks a₁ a₂ a₃ G :=
  mng_corridorCover_of_mengerCover h

-- The routing cover is a Menger core on each configuration of the event.
example (n : ℕ) (h : MengerRoutingCover 2 n) (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ threeMeetBox 2 n) : MengerCore ω :=
  h ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MengerRouting
