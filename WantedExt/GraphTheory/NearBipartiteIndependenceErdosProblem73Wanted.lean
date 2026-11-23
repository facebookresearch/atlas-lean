/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graphs with large independent sets in every subgraph (Erdős Problem 73)

Erdős Problem 73: let `k ≥ 0` and let every subgraph `H` of `G` contain an independent set of size
at least `(n - k)/2`, `n = |H|`. Must `G` be the union of a bipartite graph and `O_k(1)` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.NearBipartiteIndependenceErdosProblem73Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #73, https://www.erdosproblems.com/73 (status PROVED).
UnsolvedMath record UM-30006712 (`EP-73`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite. The hypothesis is stated for induced subgraphs (vertex sets `S`), which is
equivalent: deleting edges only enlarges independent sets. "Union of a bipartite graph and `O_k(1)`
vertices" is: deleting at most `C(k)` vertices leaves a 2-colorable graph. Compared with the
formal-conjectures statement `ErdosProblems/73.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 73: for every `k ≥ 0` there is `C(k)` such that every finite graph `G` in which
every vertex set `S` (every induced subgraph) contains an independent set of size at least
`(|S| - k) / 2` becomes bipartite after deleting at most `C(k)` vertices. -/
def nearBipartiteOfLargeIndependentSets : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (∀ S : Finset V, ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ (S.card : ℝ) - k ≤ 2 * I.card) →
      ∃ T : Finset V, T.card ≤ C ∧ (G.induce ((T : Set V)ᶜ)).Colorable 2

/--
Resolved true: Reed proved that such a graph becomes bipartite after deleting `O_k(1)` vertices;
erdosproblems.com/73 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #73,
https://www.erdosproblems.com/73 (status PROVED); resolution: B. Reed, Mangoes and blueberries,
Combinatorica 19 (1999), 267-296, erdosproblems.com/73: proved by Reed,
https://doi.org/10.1007/s004930050056.
-/
public theorem_wanted nearBipartiteOfLargeIndependentSets_holds :
    nearBipartiteOfLargeIndependentSets

end MathlibExt.GraphTheory.NearBipartiteIndependenceErdosProblem73Wanted
