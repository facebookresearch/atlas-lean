/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs

/-!
# Proper colorings of finite hypergraphs

`HypergraphColorable` expresses that every edge has two differently colored vertices.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.HypergraphColoringShared

/-- **Colorable hypergraph.** A hypergraph $H$ on the vertex set $\{0, \dots, n-1\}$, given as a
finite set of edges (sets of vertices), is $k$-colorable when some coloring of the vertices with
$k$ colors leaves no edge monochromatic: every edge of $H$ contains two vertices of different
colors. -/
def HypergraphColorable {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

end MathlibExt.Combinatorics.HypergraphColoringShared
