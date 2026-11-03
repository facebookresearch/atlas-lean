/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFree`

* `bmf_omegaTri_mem_X`: the three-ray configuration `bmf_omegaTri` lies in the precursor event
  `bmf_X` (three infinite, pairwise separated clusters after removing the origin), so `bmf_X` is
  nonempty (instance).
* `bmf_walk_invariant`: open walks in `bmf_omegaTri` starting on the ray `bmf_R₁` stay on it.
* The forced pattern `bmf_η₀` opens all three edges of `bmf_I`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The three-ray configuration is in the precursor event.
example : bmf_omegaTri ∈ bmf_X ∧ bmf_X.Nonempty :=
  ⟨bmf_omegaTri_mem_X, bmf_X_nonempty⟩

-- Its three ray clusters stay infinite after removing the origin.
example : (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂).Infinite :=
  bmf_omegaTri_mem_X.1.2.1

-- Walks inside a set closed under open edges stay in it (the whole lattice, here).
example {x y : Site 2} (w : (openSubgraph 2 bmf_omegaTri).Walk x y) : y ∈ (Set.univ : Set _) :=
  bmf_walk_invariant (S := Set.univ) (fun _ _ _ _ => trivial) w trivial

-- The pattern `bmf_η₀` opens every edge of `bmf_I`.
example (e : ↥bmf_I) : bmf_η₀ e = true := rfl

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFree
