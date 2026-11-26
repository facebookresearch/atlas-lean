/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.CrossEdgeMatchingForms

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.CrossEdgeMatchingForms`

* `dow_odd_count_iff_mem_of_nodup` on the explicit list `[1, 2, 3]`;
* `dow_unitSquare_bridgeBody` converts `rpc_unitSquare_flip` into odd crossing-edge parity;
* `dow_bridge_iff_bdEdge_shared_mem` and `dow_bridge_iff_hardGap_and_reverse` apply to the empty
  walk, which satisfies the crossing-edge matching.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.CrossEdgeMatchingForms

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

-- On a list without duplicates, an odd count is membership.
example : Odd (List.count 2 [1, 2, 3]) :=
  (dow_odd_count_iff_mem_of_nodup (l := [1, 2, 3]) (by decide) 2).mpr (by decide)

-- The unit-square instance: the top edge of the cell is a boundary edge, so the crossing edge is
-- traversed an odd number of times.
example : Odd (List.count (rpc_crossEdge ![0, 1] ![1, 1]) wwit_unitSquareLoop.edges) :=
  dow_unitSquare_bridgeBody.mpr rpc_unitSquare_flip

-- The equivalent forms of the crossing-edge matching, specialised to any closed walk.
example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (h : rpc_CrossEdgeOddIffOnWalk Vc)
    {u v : Site 2} (huv : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges :=
  (dow_bridge_iff_bdEdge_shared_mem Vc).mp h huv

-- For a walk without repeated edges, the matching splits into `jbw_hard_gap` and its converse.
example {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup)
    (h : rpc_CrossEdgeOddIffOnWalk Vc) : jbw_hard_gap Vc :=
  ((dow_bridge_iff_hardGap_and_reverse Vc hnd).mp h).1

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.CrossEdgeMatchingForms
