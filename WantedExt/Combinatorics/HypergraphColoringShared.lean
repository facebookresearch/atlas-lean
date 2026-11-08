/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared hypergraph coloring predicate

Proper vertex colorings of finite hypergraphs (no monochromatic edge), shared by the WantedExt
entries for Erdős Problems 832 and 833 so that both speak about the same notion of chromatic
number.
-/

module

public import Mathlib.Data.Finset.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.HypergraphColoringShared

/-- A hypergraph `H` on `Fin n` (a finite set of edges) is `k`-colorable: some coloring of the
vertices with `k` colors leaves no edge monochromatic. -/
def HypergraphColorable {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ c : Fin n → Fin k, ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

end MathlibExt.Combinatorics.HypergraphColoringShared
