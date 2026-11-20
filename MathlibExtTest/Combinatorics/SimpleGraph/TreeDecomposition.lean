/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TreeDecomposition
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MathlibExtTest.Combinatorics.SimpleGraph.TreeDecomposition

open _root_.SimpleGraph

-- tw(K₄) = 3: at most 3 ...
example : (⊤ : SimpleGraph (Fin 4)).HasTreewidthAtMost 3 :=
  hasTreewidthAtMost_top_iff.mpr (by simp)

-- ... and not at most 2.
example : ¬(⊤ : SimpleGraph (Fin 4)).HasTreewidthAtMost 2 := by
  rw [hasTreewidthAtMost_top_iff]
  simp

-- The graph with no vertices has tree-width at most every k (its tree-width is -1).
example (G : SimpleGraph (Fin 0)) (k : ℕ) : G.HasTreewidthAtMost k :=
  hasTreewidthAtMost_of_encard_le G (by simp)

-- A path on five vertices is a tree, so it has tree-width exactly one.
example : (pathGraph 5).HasTreewidthAtMost 1 :=
  (isTree_pathGraph.mpr (by decide)).hasTreewidthAtMost_one

example : ¬(pathGraph 5).HasTreewidthAtMost 0 :=
  not_hasTreewidthAtMost_zero_of_adj (u := 0) (v := 1) (by simp [pathGraph_adj])

-- Every clique of a decomposed graph lies in a bag.
example (G : SimpleGraph (Fin 6)) (D : G.TreeDecomposition) (K : Finset (Fin 6))
    (hK : ∀ u ∈ K, ∀ w ∈ K, u ≠ w → G.Adj u w) : ∃ t, (K : Set (Fin 6)) ⊆ D.bag t :=
  D.exists_bag_superset K hK

end MathlibExtTest.Combinatorics.SimpleGraph.TreeDecomposition
