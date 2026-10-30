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

/-- `ex₃(n, 𝓕_k)`: the largest number of triples of a `3`-uniform hypergraph on `Fin n`
(`SetFamily.IsUniform E 3`) containing no member of `𝓕_k`, the family of all `3`-graphs with `k`
vertices and `k - 2` edges (the literal, single-`k` family of the problem). Containing a member of
`𝓕_k` is `SetFamily.ContainsSubgraph E k (k - 2)`: some `k` vertices span at least `k - 2`
triples (a member may have isolated vertices, and extra triples can be dropped). -/
noncomputable def exSingle (k n : ℕ) : ℕ :=
  sSup {m | ∃ E : Finset (Finset (Fin n)), SetFamily.IsUniform E 3 ∧
    ¬ SetFamily.ContainsSubgraph E k (k - 2) ∧ E.card = m}

/-- Erdős Problem 1076 as worded: for every `k ≥ 5`, `ex₃(n, 𝓕_k) ∼ n² / 6`, with `𝓕_k` the
single family of `3`-graphs with `k` vertices and `k - 2` edges. -/
def singleFamilyAsymptotic : Prop :=
  ∀ k : ℕ, 5 ≤ k → Tendsto (fun n : ℕ => (exSingle k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6))

/--
Resolved false as worded: for `k = 5`, Glock proved that the largest triple system on `n` vertices
with no five vertices spanning three triples has `(1 + o(1)) n² / 5` triples, so `ex₃(n, 𝓕_5) / n²
→ 1/5`, not `1/6`; his §1 states this as the answer to whether `1/6` is sharp for every `k`.
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
