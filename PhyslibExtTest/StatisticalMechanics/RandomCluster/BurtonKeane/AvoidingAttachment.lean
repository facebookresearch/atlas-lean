/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment`

* `ava_origin_no_adj_removeSite` for the all-open configuration of `ℤ²`;
* `ava_connected_origin_eq` and `ava_avoidingRoutingResidue_of_neighbour` in conditional form;
* `ava_disjointRouting_of_boxResidue` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- After removing the origin it has no open neighbour (all-open configuration).
example (y : Site 2) : ¬ (openSubgraph 2 (removeSite 0 (fun _ => true))).Adj 0 y :=
  ava_origin_no_adj_removeSite _ y

-- After removing the origin, the origin is connected only to itself.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (h : Connected d (removeSite 0 ω) (0 : Site d) x) : x = 0 :=
  ava_connected_origin_eq ω h

-- A neighbour of the origin with an infinite cluster satisfies the routing residue.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x) (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x :=
  ava_avoidingAttachment ω x (ava_avoidingRoutingResidue_of_neighbour ω x hadj hri)

-- The box residue gives disjoint routing.
example {d n : ℕ} (h : ava_BoxAvoidingRoutingResidue d n) : hrHD_DisjointRouting d n :=
  ava_disjointRouting_of_boxResidue h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AvoidingAttachment
