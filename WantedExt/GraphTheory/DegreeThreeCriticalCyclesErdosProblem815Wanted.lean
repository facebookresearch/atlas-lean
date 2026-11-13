/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cycles in degree `3`-critical graphs (Erdős Problem 815)

Erdős Problem 815 (Erdős and Hajnal): let `k ≥ 3` and `n` be sufficiently large. Must every graph
`G` with `n` vertices and `2n - 2` edges, every proper induced subgraph of which has minimum degree
at most `2`, contain a copy of `C_k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.DegreeThreeCriticalCyclesErdosProblem815Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #815, https://www.erdosproblems.com/815 (status
DISPROVED). UnsolvedMath record UM-30007047 (`EP-815`), dataset ulamai/UnsolvedMath v1.8.0.

Such graphs are called degree `3`-critical. A proper induced subgraph is induced on a nonempty
vertex set `S ≠ V`; minimum degree at most `2` means some vertex of `S` has at most two neighbors in
`S`. A copy of `C_k` is a cycle of length `k` (`Walk.IsCycle`). formal-conjectures has no statement
of this problem.
-/

open Classical in
/-- `G` is degree `3`-critical: it has `2n - 2` edges and every nonempty proper vertex subset
induces a subgraph with a vertex of degree at most `2`. -/
def IsDegreeThreeCritical {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.edgeSet.ncard = 2 * n - 2 ∧ ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2

/-- Erdős Problem 815: for every `k ≥ 3` and all large `n`, every degree `3`-critical graph on `n`
vertices contains a cycle of length `k`. -/
def degreeThreeCriticalContainsCycles : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n), IsDegreeThreeCritical G →
    ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = k

/--
Resolved false: Narins, Pokrovskiy and Szabó constructed arbitrarily large degree `3`-critical
graphs with no cycle of length `23`; erdosproblems.com/815 lists the problem as disproved (the case
of even `k` remains open). Source: T. F. Bloom, Erdős Problems, Problem #815,
https://www.erdosproblems.com/815 (status DISPROVED); resolution: L. Narins, A. Pokrovskiy and T.
Szabó, Graphs without proper subgraphs of minimum degree 3 and short cycles, Combinatorica (2017),
495-519, arXiv:1408.5289, Theorem 1.2: there is an infinite sequence of degree 3-critical graphs (n
vertices, 2n - 2 edges, no proper induced subgraph of minimum degree 3) none of which contains a
cycle of length 23, disproving the conjecture of Erdős, Faudree, Gyárfás and Schelp,
https://arxiv.org/abs/1408.5289.
-/
public theorem_wanted degreeThreeCriticalContainsCycles_refuted :
    ¬ degreeThreeCriticalContainsCycles

end MathlibExt.GraphTheory.DegreeThreeCriticalCyclesErdosProblem815Wanted
