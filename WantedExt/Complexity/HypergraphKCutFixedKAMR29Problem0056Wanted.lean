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
/-- The decision version of hypergraph `k`-cut. An input decodes to `(n, (E, B))`: vertices
`0, …, n - 1`, hyperedges `E` given as (vertex list, natural cost) pairs, and a budget `B`. It is
accepted iff every hyperedge lists vertices below `n` and some partition of the vertices into `k`
non-empty parts (a surjection `f` onto `0, …, k - 1`) has total cost of the hyperedges meeting two
parts at most `B`. -/
noncomputable def hypergraphKCutDec (k : ℕ) : DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := ℕ × (List (List ℕ × ℕ) × ℕ)) x with
  | some (n, (E, B)) => decide (
      (∀ e ∈ E, ∀ v ∈ e.1, v < n) ∧
      ∃ f : ℕ → ℕ, (∀ v < n, f v < k) ∧ (∀ j < k, ∃ v < n, f v = j) ∧
        ((E.filter fun e => ∃ u ∈ e.1, ∃ v ∈ e.1, f u ≠ f v).map Prod.snd).sum ≤ B)
  | none => false

/-- For every fixed `k`, hypergraph `k`-cut with non-negative integer costs is decidable in
polynomial time. -/
def hypergraphKCutInP : Prop :=
  ∀ k : ℕ, hypergraphKCutDec k ∈ P

/--
Resolved true: Chandrasekaran and Chekuri give, for every fixed `k`, a deterministic polynomial-time
algorithm for hypergraph `k`-cut with non-negative hyperedge costs, so the decision version (is
there a `k`-cut of cost at most `B`) is in `P`. Source: EGRES Open (Egerváry Research Group), list
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
