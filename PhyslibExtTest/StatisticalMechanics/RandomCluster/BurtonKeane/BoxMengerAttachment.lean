/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerAttachment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerAttachment`

* `bma_originAvoiding_union` and `bma_internal_of_edgesIn` on explicit (empty) edge sets;
* `bma_clusterAttachment_of_neighbour` in conditional form;
* `bma_disjointRouting_of_clusterAttachment` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerAttachment

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- The union of origin-avoiding edge sets avoids the origin (empty sets).
example : ∀ e ∈ (∅ ∪ ∅ ∪ ∅ : Finset (Sym2 (Site 2))), (0 : Site 2) ∉ e :=
  bma_originAvoiding_union (by simp) (by simp) (by simp)

-- Edges inside a region keep a walk in the region (empty edge set).
example (R : Set (Site 2)) : ∀ u v, u ∈ R → s(u, v) ∈ (∅ : Finset (Sym2 (Site 2))) → v ∈ R :=
  bma_internal_of_edgesIn (by simp)

-- A neighbour of the origin with an infinite cluster has a cluster attachment.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x) (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    bma_ClusterAttachment ω x :=
  bma_clusterAttachment_of_neighbour ω x hadj hri

-- Box cluster attachment gives disjoint routing.
example {d n : ℕ} (h : bma_BoxClusterAttachment d n) : hrHD_DisjointRouting d n :=
  bma_disjointRouting_of_clusterAttachment h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerAttachment
