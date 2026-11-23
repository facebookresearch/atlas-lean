/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triple systems with few triples on every small vertex set (Erdős Problem 1076)

Erdős Problem 1076: let `k ≥ 5` and let `𝓕_k` be the family of all `3`-uniform hypergraphs with
`k` vertices and `k - 2` edges. Is it true that `ex₃(n, 𝓕_k) ∼ n² / 6`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph

@[expose] public section

namespace MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1076, https://www.erdosproblems.com/1076 (status
PROVED). UnsolvedMath record UM-30007153 (`EP-1076`), dataset ulamai/UnsolvedMath v1.8.0.

A triple system on `n` vertices is a `3`-uniform family of subsets of `Fin n` (MathlibExt's
`SetFamily.IsUniform`). It contains a member of `𝓕_k` exactly when some `k` vertices span at least
`k - 2` triples (MathlibExt's `SetFamily.ContainsSubgraph`; a member may have isolated vertices,
and extra triples can be dropped), so `ex₃(n, 𝓕_k)` is Brown-Erdős-Sós's `f⁽³⁾(n; k, k - 2)`.
Glock's theorem gives `f⁽³⁾(n; 5, 3) = (1 + o(1)) n² / 5`, so the claim as worded fails at `k =
5`; his §1 asks exactly whether the lower bound `1/6` is sharp for every `k` (it is for `k = 4`,
by Brown, Erdős and Sós). The page lists the problem as proved, saying that the asymptotic version
'asked for here' was proved by Bohman and Warnke and by Glock, Kühn, Lo and Osthus. Their theorem
forbids `j` vertices with `j - 2` triples for every `4 ≤ j ≤ k` at once (partial Steiner triple
systems of girth larger than `k`), and both papers present it as the answer to Erdős's 1973
question on high-girth Steiner triple systems (Problems and results in combinatorial analysis,
Rome 1973), not to this problem, so that reading is not stated here. The teorth/erdosproblems
database note on a Lean contribution separates the same two readings (positive under simultaneous
sparsity, negative for the literal single-`k` reading). formal-conjectures has no statement of
this problem.
-/

open Filter Topology

/-- **Extremal number for $k$ vertices spanning $k - 2$ triples.** For $k, n \in \mathbb{N}$ let
$\mathcal{F}_k$ be the family of all $3$-uniform hypergraphs with $k$ vertices and $k - 2$ edges.
Then $\mathrm{ex}_3(n, \mathcal{F}_k)$ is the largest number of triples in a $3$-uniform
hypergraph $E$ on the vertex set $\{0, \dots, n-1\}$ that contains no member of $\mathcal{F}_k$,
meaning that no set of exactly $k$ vertices contains $k - 2$ or more triples of $E$ (a member may
have isolated vertices, and extra triples can be dropped). Here $k - 2$ is read as $0$ when
$k < 2$, and $\mathrm{ex}_3(n, \mathcal{F}_k) = 0$ when no such hypergraph exists, which happens
exactly when $k \le 2$ and $k \le n$. -/
noncomputable def exSingle (k n : ℕ) : ℕ :=
  sSup {m | ∃ E : Finset (Finset (Fin n)), SetFamily.IsUniform E 3 ∧
    ¬ SetFamily.ContainsSubgraph E k (k - 2) ∧ E.card = m}

/-- **Erdős Problem 1076 as worded.** For $k, n \in \mathbb{N}$ let
$\mathrm{ex}_3(n, \mathcal{F}_k)$ be the largest number of triples in a $3$-uniform hypergraph on
$n$ vertices in which no $k$ vertices span $k - 2$ or more triples, that is, which contains no
member of the family $\mathcal{F}_k$ of $3$-graphs with $k$ vertices and $k - 2$ edges. This is
the statement that for every $k \ge 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) / n^2 \to 1/6$ as
$n \to \infty$, that is, $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$. -/
def singleFamilyAsymptotic : Prop :=
  ∀ k : ℕ, 5 ≤ k → Tendsto (fun n : ℕ => (exSingle k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6))

/--
**Erdős Problem 1076 fails as worded.** For $k, n \in \mathbb{N}$ let $\mathcal{F}_k$ be the family
of $3$-graphs with $k$ vertices and $k - 2$ edges, and let $\mathrm{ex}_3(n, \mathcal{F}_k)$ be the
largest number of triples in a $3$-uniform hypergraph on $n$ vertices that contains no member of
$\mathcal{F}_k$, that is, in which no $k$ vertices span $k - 2$ or more triples. It is not true
that for every $k \ge 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) / n^2 \to 1/6$ as $n \to \infty$.

Already $k = 5$ fails: Glock proved that the largest triple system on $n$ vertices with no five
vertices spanning three triples has $(1 + o(1)) n^2 / 5$ triples, so
$\mathrm{ex}_3(n, \mathcal{F}_5) / n^2 \to 1/5$; his §1 states this as the answer to whether $1/6$
is sharp for every $k$.

Source: T. F. Bloom, Erdős Problems, Problem #1076, https://www.erdosproblems.com/1076 (status
PROVED); resolution: S. Glock, Triple systems with no three triples spanning at most five points,
Bull. Lond. Math. Soc. 51 (2019), 230-236, abstract and Theorem 2: lim n⁻² f⁽³⁾(n; 5, 3) = 1/5,
where f⁽³⁾(n; k, s) is the largest number of triples on n points containing no k points spanning s
triples; §1 poses the question whether the lower bound lim inf n⁻² f⁽³⁾(n; k, k - 2) ≥ 1/6 is
sharp in general, and Theorem 2 shows it is not for k = 5 (arXiv:1809.02100),
https://arxiv.org/abs/1809.02100.
-/
public theorem_wanted singleFamilyAsymptotic_refuted : ¬ singleFamilyAsymptotic

end MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted
