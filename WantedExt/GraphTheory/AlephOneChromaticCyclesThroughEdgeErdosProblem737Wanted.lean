/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cycles through one edge in graphs of chromatic number `ℵ₁` (Erdős Problem 737)

Erdős Problem 737 (Erdős, Hajnal and Shelah): let `G` be a graph with chromatic number `ℵ₁`. Must
there exist an edge `e` such that, for all large `n`, `G` contains a cycle of length `n` containing
`e`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

namespace MathlibExt.GraphTheory.AlephOneChromaticCyclesThroughEdgeErdosProblem737Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #737, https://www.erdosproblems.com/737 (status
PROVED). UnsolvedMath record UM-30007002 (`EP-737`), dataset ulamai/UnsolvedMath v1.8.0.

Chromatic number `ℵ₁` is stated through colourings: no proper colouring by `ℕ`, and a proper
colouring by a type of cardinality `ℵ₁`. Vertex types are in `Type`. A cycle of length `n`
containing `e = uv` is a closed walk with `Walk.IsCycle`, length `n` and `s(u, v)` among its edges.
-/

/-- Erdős Problem 737 (Erdős, Hajnal and Shelah): every graph `G` with chromatic number `ℵ₁` (no
proper colouring with countably many colours, and a proper colouring with `ℵ₁` colours) has an
edge `e` such that for all sufficiently large `n` some cycle of length `n` in `G` passes through
`e`. -/
def alephOneChromaticEdgeInAllLargeCycles : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
    (∃ α : Type, Cardinal.mk α = Cardinal.aleph 1 ∧ Nonempty (G.Coloring α)) →
      ∃ u v : V, G.Adj u v ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        ∃ (w : V) (p : G.Walk w w), p.IsCycle ∧ p.length = n ∧ s(u, v) ∈ p.edges

/--
Resolved true: Thomassen proved that a graph of chromatic number `ℵ₁` has an edge contained in
cycles of every sufficiently large length; erdosproblems.com/737 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #737, https://www.erdosproblems.com/737 (status
PROVED); resolution: C. Thomassen, Cycles in graphs of uncountable chromatic number, Combinatorica 3
(1983), 133-134, erdosproblems.com/737: 'This is true, and was proved by Thomassen' (Erdős, Hajnal
and Shelah had proved that G contains all sufficiently large cycles),
https://www.erdosproblems.com/737.
-/
public theorem_wanted alephOneChromaticEdgeInAllLargeCycles_holds :
    alephOneChromaticEdgeInAllLargeCycles

end MathlibExt.GraphTheory.AlephOneChromaticCyclesThroughEdgeErdosProblem737Wanted
