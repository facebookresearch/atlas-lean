/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum k-way cut in a hypergraph for fixed k (EGRES open problem)

EGRES Open, Minimum k-way cut in a hypergraph: can we find a minimum `k`-way cut in a capacitated
hypergraph in polynomial time, if `k` is fixed?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MathlibExt.Complexity.HypergraphKCutFixedKAMR29Problem0056Wanted

/-!
Source: EGRES Open (Egerváry Research Group), list of open problems, Minimum k-way cut in a
hypergraph, https://oldlemon.cs.elte.hu/egres/open/Minimum_k-way_cut_in_a_hypergraph. UnsolvedMath
record UM-03000056 (`AMR-029-0056`), dataset ulamai/UnsolvedMath v1.8.0.

Stated as membership in the repository's bitstring class `P` of the decision version, as in
`WantedExt/Complexity/KeyTheorems/*InPWanted.lean`: given a hypergraph on `0, …, n - 1` with
non-negative integer hyperedge costs and a budget `B`, is there a partition of the vertices into `k`
non-empty parts whose crossing hyperedges cost at most `B` (the partition formulation of a `k`-cut
used by Chandrasekaran and Chekuri)? A polynomial-time algorithm that finds a minimum `k`-cut
decides this; the search question itself is not formalized.
-/

open MetaMathlibExt.ComplexityTheory

open Classical in
/-- **Decision version of hypergraph $k$-cut.** For a natural number $k$, this is the decision
problem on bitstrings that decodes an input as a triple $(n, E, B)$: a number $n$ of vertices
$0, \dots, n-1$, a list $E$ of hyperedges, each a list of vertices with a natural-number cost, and
a natural-number budget $B$. It accepts the input iff every hyperedge lists only vertices below
$n$ and there is a partition of the vertices into $k$ non-empty parts, given by a map $f$ from
$\{0, \dots, n-1\}$ onto $\{0, \dots, k-1\}$, such that the total cost of the hyperedges in $E$
(counted with multiplicity) that meet two different parts is at most $B$. Inputs that do not
decode are rejected. -/
noncomputable def hypergraphKCutDec (k : ℕ) : DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × (List (List ℕ × ℕ) × ℕ)) x with
  | some (n, (E, B)) => decide (
      (∀ e ∈ E, ∀ v ∈ e.1, v < n) ∧
      ∃ f : ℕ → ℕ, (∀ v < n, f v < k) ∧ (∀ j < k, ∃ v < n, f v = j) ∧
        ((E.filter fun e => ∃ u ∈ e.1, ∃ v ∈ e.1, f u ≠ f v).map Prod.snd).sum ≤ B)
  | none => false

/-- **The EGRES question on hypergraph $k$-cut for fixed $k$.** The statement that for every natural
number $k$, the decision version of hypergraph $k$-cut is in the complexity class P. That problem
accepts a hypergraph on the vertices $0, \dots, n-1$, given by hyperedges with natural-number
costs, and a budget $B$ iff every hyperedge lists only vertices below $n$ and some partition of the
vertices into $k$ non-empty parts has total cost of the hyperedges meeting two parts at most $B$;
inputs that do not decode are rejected. -/
def hypergraphKCutInP : Prop :=
  ∀ k : ℕ, hypergraphKCutDec k ∈ P

/--
**Hypergraph $k$-cut for fixed $k$ is in P.** For every natural number $k$, the decision version
of hypergraph $k$-cut is in the complexity class P. That problem accepts a hypergraph on the
vertices $0, \dots, n-1$, given by hyperedges with natural-number costs, and a budget $B$ iff every
hyperedge lists only vertices below $n$ and some partition of the vertices into $k$ non-empty parts
has total cost of the hyperedges meeting two parts at most $B$; inputs that do not decode are
rejected.

Chandrasekaran and Chekuri give, for every fixed $k$, a deterministic polynomial-time algorithm for
hypergraph $k$-cut with non-negative hyperedge costs, which decides this problem.

Source: EGRES Open (Egerváry Research Group), list
of open problems, Minimum k-way cut in a hypergraph,
https://oldlemon.cs.elte.hu/egres/open/Minimum_k-way_cut_in_a_hypergraph; resolution: K.
Chandrasekaran and C. Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, FOCS
2020; arXiv:2009.12442, abstract: for hypergraphs with non-negative hyperedge costs and fixed k, a
deterministic polynomial-time algorithm for Hypergraph-k-cut (a least-cost F ⊆ E such that G - F has
at least k components, equivalently a partition of V into k non-empty parts minimizing the cost of
crossing hyperedges), https://arxiv.org/abs/2009.12442.
-/
public theorem_wanted hypergraphKCutInP_holds : hypergraphKCutInP

end MathlibExt.Complexity.HypergraphKCutFixedKAMR29Problem0056Wanted
