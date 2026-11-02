/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.ShiftSquareCycle

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.KramersWannier.ShiftSquareCycle`

* `ceo_shiftSquare` has no repeated edges;
* `ceo_shiftSquare_residue_false` refutes `rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare`;
* `ceo_primalWalkLeftRegionMatch_false` refutes `kwc_PrimalWalkLeftRegionMatch`, and with it the
  hypothesis of `rpc_primalWalkLeftRegionMatch_of_bridge`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.ShiftSquareCycle

open _root_.StatMech _root_.StatMech.Walls _root_.StatMech.Lattice

-- The loop has no repeated edges.
example : ceo_shiftSquare.edges.Nodup := ceo_shiftSquare_edges_nodup

-- The crossing-edge matching fails for the loop.
example : ¬ rpc_CrossEdgeOddIffOnWalk ceo_shiftSquare := ceo_shiftSquare_residue_false

-- The inside-region matching is false.
example : ¬ kwc_PrimalWalkLeftRegionMatch := ceo_primalWalkLeftRegionMatch_false

-- Hence the crossing-edge matching fails for some closed walk.
example : ¬ ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), rpc_CrossEdgeOddIffOnWalk Vc :=
  fun h => ceo_shiftSquare_residue_false (h ceo_shiftSquare)

end PhyslibExtTest.CondensedMatter.IsingModel.KramersWannier.ShiftSquareCycle
