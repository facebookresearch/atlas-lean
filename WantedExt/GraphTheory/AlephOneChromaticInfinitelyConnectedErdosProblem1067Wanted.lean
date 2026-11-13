/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Infinitely connected subgraphs of `ℵ₁`-chromatic graphs (Erdős Problem 1067)

Erdős Problem 1067 (Erdős and Hajnal): does every graph with chromatic number `ℵ₁` contain an
infinitely connected subgraph with chromatic number `ℵ₁`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.SetTheory.Cardinal.Aleph
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.AlephOneChromaticInfinitelyConnectedErdosProblem1067Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1067, https://www.erdosproblems.com/1067 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007151 (`EP-1067`), dataset ulamai/UnsolvedMath v1.8.0.

Chromatic number `ℵ₁` is `MathlibExt`'s `SimpleGraph.chromaticCardinal G = ℵ₁` (the least
cardinality of a color type of a proper coloring). Infinitely connected means any two distinct
vertices are joined by infinitely many distinct paths that share only their ends, as on the page.
Subgraphs are taken induced, which is equivalent (see the target). Vertex types are in `Type`.
Compared with the formal-conjectures statement `ErdosProblems/1067.lean` (equivalent; no code
imported).
-/

/-- `G` is infinitely connected: any two distinct vertices are joined by infinitely many distinct
paths, any two of which share no vertex other than the two ends. -/
def IsInfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ P : ℕ → G.Walk u v, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ w ∈ (P i).support, w ∈ (P j).support → w = u ∨ w = v

/-- Erdős Problem 1067 (Erdős and Hajnal): every graph with chromatic number `ℵ₁` has an infinitely
connected subgraph with chromatic number `ℵ₁`. Induced subgraphs suffice: adding the remaining
edges between its vertices keeps such a subgraph infinitely connected and of chromatic number
`ℵ₁`. -/
def alephOneChromaticHasInfinitelyConnectedSubgraph : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = Cardinal.aleph 1 →
    ∃ W : Set V, (G.induce W).chromaticCardinal = Cardinal.aleph 1 ∧
      IsInfinitelyConnected (G.induce W)

/--
Resolved false: Soukup constructed in ZFC a graph of chromatic number `ℵ₁` with no infinitely
connected subgraph of chromatic number `ℵ₁` (after Komjáth's consistency result); Bowler and Pitz
gave an elementary uncountably chromatic graph without uncountable infinitely connected subgraphs.
erdosproblems.com/1067 lists the problem as disproved (Lean). Source: T. F. Bloom, Erdős Problems,
Problem #1067, https://www.erdosproblems.com/1067 (status DISPROVED (LEAN)); resolution: D. T.
Soukup, Trees, ladders and graphs, J. Combin. Theory Ser. B (2015), 96-116; N. Bowler and M. Pitz, A
note on uncountably chromatic graphs, arXiv:2402.05984 (2024), Soukup: a ZFC counterexample;
Bowler-Pitz: an elementary uncountably chromatic graph without uncountable infinitely connected
subgraphs (erdosproblems.com/1067), https://arxiv.org/abs/2402.05984.
-/
public theorem_wanted alephOneChromaticHasInfinitelyConnectedSubgraph_refuted :
    ¬ alephOneChromaticHasInfinitelyConnectedSubgraph

end MathlibExt.GraphTheory.AlephOneChromaticInfinitelyConnectedErdosProblem1067Wanted
