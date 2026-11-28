/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachment`

* `cla_walk_survival_force` with the trivial walk at a site other than the origin;
* `cla_clusterAttachment_of_avoidingAttachment` composed with
  `cla_avoidingAttachment_of_neighbour`, in conditional form;
* `cla_disjointRouting_of_boxAvoiding` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachment

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- The trivial walk survives forcing and removing the origin.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (W : Finset (Sym2 (Site d))) (a : Site d)
    (ha : (0 : Site d) ≠ a) : Connected d (removeSite 0 (forceOpenFinset W ω)) a a :=
  cla_walk_survival_force ω W .nil (by simpa using ha)

-- A neighbour of the origin with an infinite cut cluster has a cluster attachment.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x) (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x (cla_avoidingAttachment_of_neighbour ω x hadj hri)

-- Box avoiding attachment gives disjoint routing.
example {d n : ℕ} (h : cla_BoxAvoidingAttachment d n) : hrHD_DisjointRouting d n :=
  cla_disjointRouting_of_boxAvoiding h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ClusterAttachment
