/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger`

* `bmm_cluster_omegaClosed` for the all-open configuration of `ℤ²`;
* `bmm_distinct_neighbours_of_disjoint_regions` with the regions `{0}` and `{0}ᶜ`;
* `bmm_disjointRouting_of_attachment` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Clusters are closed under open edges (all-open configuration).
example (x : Site 2) : ∀ u v, u ∈ cluster 2 (fun _ => true) x →
    IsOpenEdge 2 (fun _ => true) u v → v ∈ cluster 2 (fun _ => true) x :=
  bmm_cluster_omegaClosed _ x

-- Sites in disjoint regions are distinct.
example (b : Site 2) (hb : b ≠ 0) : (0 : Site 2) ≠ b :=
  bmm_distinct_neighbours_of_disjoint_regions (R := {0}) (S := {0}ᶜ) rfl hb
    disjoint_compl_right

-- The Menger attachment gives disjoint routing.
example {d n : ℕ} (h : bmm_BoxMengerAttachment d n) : hrHD_DisjointRouting d n :=
  bmm_disjointRouting_of_attachment h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMergeFreeMenger
