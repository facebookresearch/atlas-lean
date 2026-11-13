/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cycles with many chords at one vertex (Erdős Problem 767)

Erdős Problem 767: let `g_k(n)` be the maximal number of edges of a graph on `n` vertices that does
not contain a cycle with `k` chords incident to a vertex on the cycle. Is `g_k(n) = (k + 1) n - (k +
1)²` for `n` sufficiently large?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.CycleIncidentChordsErdosProblem767Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #767, https://www.erdosproblems.com/767 (status
PROVED). UnsolvedMath record UM-30007024 (`EP-767`), dataset ulamai/UnsolvedMath v1.8.0.

A chord of a cycle at a cycle vertex `v` is an edge `v w` of the graph with `w` on the cycle that is
not an edge of the cycle; the cycle has `k` chords at `v` when `k` distinct such `w` exist
(containing a cycle with at least `k` chords at a vertex). `g_k(n) = (k + 1) n - (k + 1)²` is stated
as an upper bound for all such graphs on `Fin n` and attainment by one of them, for `k ≥ 1` and all
large `n` (`K_{k+1, n-k-1}` attains it). Compared with the formal-conjectures statement
`ErdosProblems/767.lean` (formal-conjectures states Jiang's explicit range `n ≥ 3k + 3`; this module
states the problem's 'n sufficiently large'; no code imported).
-/

/-- `G` contains a cycle through a vertex `v` together with `k` distinct chords of the cycle at `v`:
edges `v w` of `G` with `w` on the cycle that are not edges of the cycle. -/
def HasCycleWithIncidentChords {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∃ S : Finset V, S.card = k ∧
    ∀ w ∈ S, G.Adj v w ∧ w ∈ c.support ∧ s(v, w) ∉ c.edges

/-- Erdős Problem 767: for every `k ≥ 1` and all large `n`, the largest number of edges of a graph
on `n` vertices with no cycle having `k` chords at one of its vertices is `(k + 1) n - (k + 1)²`. -/
def incidentChordsExtremalNumber : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ᶠ n : ℕ in Filter.atTop,
    (∀ G : SimpleGraph (Fin n), ¬ HasCycleWithIncidentChords G k →
      G.edgeSet.ncard ≤ (k + 1) * n - (k + 1) ^ 2) ∧
    ∃ G : SimpleGraph (Fin n), ¬ HasCycleWithIncidentChords G k ∧
      G.edgeSet.ncard = (k + 1) * n - (k + 1) ^ 2

/--
Resolved true: Jiang proved `g_k(n) = (k + 1) n - (k + 1)²` for every positive `k` and all `n ≥ 3k +
3` (Pósa had the case `g_1(n) = 2n - 4` for `n ≥ 4`); erdosproblems.com/767 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #767, https://www.erdosproblems.com/767 (status
PROVED); resolution: T. Jiang, A note on a conjecture about cycles with many incident chords, J.
Graph Theory 46 (2004), 180-182, abstract: with g_k(n) the maximum number of edges of a graph on n
vertices with no cycle having k chords incident to a vertex on the cycle, the conjecture that g_k(n)
= (k + 1)n - (k + 1)² for all n ≥ n(k) holds with n(k) ≤ 3k + 3 (positive integers n, k),
https://doi.org/10.1002/jgt.10179.
-/
public theorem_wanted incidentChordsExtremalNumber_holds : incidentChordsExtremalNumber

end MathlibExt.GraphTheory.CycleIncidentChordsErdosProblem767Wanted
