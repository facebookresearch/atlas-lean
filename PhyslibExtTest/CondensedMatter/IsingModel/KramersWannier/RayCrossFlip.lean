/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip`

* `rpc_unitSquare_flip`: the top edge of the unit cell bounds the inside of the unit-square loop;
* `rpc_crossFlip` turns it into odd parity of the crossing edge (agreeing with
  `rpc_unitSquare_crossEdge_odd`);
* `rpc_leftRegion_bdEdge_iff` applied under its hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

/-- The sites `(0, 1)` and `(1, 1)` are adjacent. -/
theorem adj01_11 : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

-- The unit-square boundary edge.
example : bdEdge (jec_leftRegion wwit_unitSquareLoop) s(![0, 1], ![1, 1]) := rpc_unitSquare_flip

-- The parity flip turns it into odd crossing-edge parity.
example : Odd (List.count (rpc_crossEdge ![0, 1] ![1, 1]) wwit_unitSquareLoop.edges) :=
  (rpc_crossFlip wwit_unitSquareLoop adj01_11).mp rpc_unitSquare_flip

-- Under the crossing-edge matching, boundary edges are the edges of the walk.
example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (h : rpc_CrossEdgeOddIffOnWalk Vc) :
    bdEdge (jec_leftRegion Vc) s(![0, 1], ![1, 1]) ↔ s(![0, 1], ![1, 1]) ∈ Vc.edges :=
  rpc_leftRegion_bdEdge_iff Vc h adj01_11

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip
