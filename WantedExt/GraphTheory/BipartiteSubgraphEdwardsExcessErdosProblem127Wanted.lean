/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Excess over Edwards' bound for bipartite subgraphs (Erdős Problem 127)

Erdős Problem 127: let `f(m)` be maximal such that every graph with `m` edges contains a bipartite
subgraph with at least `m/2 + (√(8m + 1) - 1)/8 + f(m)` edges. Is there an infinite sequence `mᵢ`
with `f(mᵢ) → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MathlibExt.GraphTheory.BipartiteSubgraphEdwardsExcessErdosProblem127Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #127, https://www.erdosproblems.com/127 (status PROVED
(LEAN)). UnsolvedMath record UM-30006732 (`EP-127`), dataset ulamai/UnsolvedMath v1.8.0.

Since every `f(m)` is finite, an infinite sequence with `f(mᵢ) → ∞` exists if and only if `f` is
unbounded, which is stated without naming `f`: for every `K` some `m` has every finite graph with
`m` edges containing a bipartite subgraph with the bound plus `K` edges. Compared with the
formal-conjectures statement `ErdosProblems/127.lean` (equivalent to `erdos_127`, whose `f` takes
integer values; no code imported).
-/

/-- Erdős Problem 127: the excess `f(m)` over Edwards' bound is unbounded: for every `K` there is
`m` such that every finite graph with `m` edges has a bipartite subgraph with at least
`m/2 + (√(8m + 1) - 1)/8 + K` edges. (Unboundedness of `f` is equivalent to `f(mᵢ) → ∞` along an
infinite sequence `mᵢ`.) -/
def edwardsExcessUnbounded : Prop :=
  ∀ K : ℝ, ∃ m : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.edgeSet.ncard = m →
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      (m : ℝ) / 2 + (Real.sqrt (8 * m + 1) - 1) / 8 + K ≤ H.edgeSet.ncard

/--
Resolved true: Alon proved `f(n²/2) ≫ n^{1/2}` (and `f(m) ≪ m^{1/4}` for all `m`), so `f` is
unbounded; Edwards had shown `f(m) ≥ 0`. erdosproblems.com/127 lists the problem as proved. Source:
T. F. Bloom, Erdős Problems, Problem #127, https://www.erdosproblems.com/127 (status PROVED (LEAN));
resolution: N. Alon, Bipartite subgraphs, Combinatorica 16 (1996), 301-311, erdosproblems.com/127:
f(n²/2) ≫ n^{1/2}, and f(m) ≪ m^{1/4} for all m.
-/
public theorem_wanted edwardsExcessUnbounded_holds : edwardsExcessUnbounded

end MathlibExt.GraphTheory.BipartiteSubgraphEdwardsExcessErdosProblem127Wanted
