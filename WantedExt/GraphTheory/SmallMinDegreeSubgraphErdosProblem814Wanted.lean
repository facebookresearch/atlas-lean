/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small subgraphs of large minimum degree (Erdős Problem 814)

Erdős Problem 814 (Erdős, Faudree, Rousseau and Schelp): let `k ≥ 2` and `G` be a graph with `n ≥ k
- 1` vertices and `(k - 1)(n - k + 2) + C(k - 2, 2) + 1` edges. Is there `c_k > 0` such that `G`
must contain an induced subgraph on at most `(1 - c_k) n` vertices with minimum degree at least `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.GraphTheory.SmallMinDegreeSubgraphErdosProblem814Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #814, https://www.erdosproblems.com/814 (status
PROVED). UnsolvedMath record UM-30007046 (`EP-814`), dataset ulamai/UnsolvedMath v1.8.0.

Stated for at least `(k - 1)(n - k + 2) + C(k - 2, 2) + 1` edges, Sauermann's form (deleting edges
reduces it to the exact count, and a subgraph of minimum degree `k` in a subgraph of `G` gives one
in `G`). `n - k + 2` is written `n + 2 - k` to avoid truncated subtraction. The induced subgraph is
on a nonempty vertex set `S`; its minimum degree is the least number of neighbors inside `S`.
Compared with the formal-conjectures statement `ErdosProblems/814.lean` (equivalent to its
`variants.at_least`; no code imported).
-/

open Classical in
/-- Erdős Problem 814: for every `k ≥ 2` there is `c_k > 0` such that every graph with `n ≥ k - 1`
vertices and at least `(k - 1)(n - k + 2) + C(k - 2, 2) + 1` edges has a nonempty vertex set of size
at most `(1 - c_k) n` inducing a subgraph of minimum degree at least `k`. -/
def smallMinDegreeSubgraph : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, k - 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1 ≤ G.edgeSet.ncard →
      ∃ S : Finset (Fin n), S.Nonempty ∧ (S.card : ℝ) ≤ (1 - c) * n ∧
        ∀ v ∈ S, k ≤ (S.filter (G.Adj v)).card

/--
Resolved true: Sauermann proved the conjecture of Erdős, Faudree, Rousseau and Schelp: every graph
on `n ≥ k - 1` vertices with at least `(k - 1)(n - k + 2) + C(k - 2, 2) + 1` edges has a subgraph on
at most `(1 - c_k) n` vertices with minimum degree at least `k`, with `c_k ≫ 1 / k³`;
erdosproblems.com/814 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#814, https://www.erdosproblems.com/814 (status PROVED); resolution: L. Sauermann, A proof of a
conjecture of Erdős, Faudree, Rousseau and Schelp on subgraphs of minimum degree k, J. Combin.
Theory Ser. B (2019), 36-75, arXiv:1705.09979, Conjecture 1.2, proved through Theorem 1.3: for every
k ≥ 2 there is ε_k > 0 such that each graph on n ≥ k - 1 vertices with (k - 1)(n - k + 2) + C(k - 2,
2) + 1 edges contains a subgraph on at most (1 - ε_k) n vertices with minimum degree at least k,
with ε_k > 1/(10^4 k³), https://arxiv.org/abs/1705.09979.
-/
public theorem_wanted smallMinDegreeSubgraph_holds : smallMinDegreeSubgraph

end MathlibExt.GraphTheory.SmallMinDegreeSubgraphErdosProblem814Wanted
