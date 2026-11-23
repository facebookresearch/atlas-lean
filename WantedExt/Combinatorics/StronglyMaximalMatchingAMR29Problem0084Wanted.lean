/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strongly maximal matchings in hypergraphs with bounded edges (EGRES open problem)

EGRES Open, Strongly maximal matchings: is it true that if all the hyperedges of a hypergraph `H`
have size at most `k` for some `k ∈ ℕ`, then `H` admits a strongly maximal matching?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted

/-!
Source: EGRES Open (Egerváry Research Group), list of open problems, Strongly maximal matchings,
https://oldlemon.cs.elte.hu/egres/open/Strongly_maximal_matchings. UnsolvedMath record UM-03000084
(`AMR-029-0084`), dataset ulamai/UnsolvedMath v1.8.0.

A hypergraph on a vertex type `V` is a set `E` of finite edges (`Finset V`); `V` and `E` may be
infinite. A matching is a set of pairwise disjoint edges, and it is strongly maximal if `|M' \ M| ≤
|M \ M'|` (cardinals) for every matching `M'`, the definition of Hollom and Randall Shaw
(Introduction), which their abstract says resolves the questions of Aharoni and others listed by
EGRES.
-/

/-- **Matching in a hypergraph.** For a hypergraph on a vertex set $V$ whose edges form a set $E$
of finite subsets of $V$, a set $M$ is a matching when $M \subseteq E$ and any two distinct
members of $M$ are disjoint. -/
def IsMatching {V : Type} (E M : Set (Finset V)) : Prop :=
  M ⊆ E ∧ M.Pairwise Disjoint

/-- **Strongly maximal matching.** For a hypergraph with edge set $E$, a set $M$ is a strongly
maximal matching (Aharoni) when $M$ is a matching of $E$ and every matching $M'$ of $E$
satisfies $|M' \setminus M| \le |M \setminus M'|$, comparing the cardinalities as cardinal
numbers. -/
def IsStronglyMaximal {V : Type} (E M : Set (Finset V)) : Prop :=
  IsMatching E M ∧ ∀ M', IsMatching E M' → Cardinal.mk ↥(M' \ M) ≤ Cardinal.mk ↥(M \ M')

/-- **Strongly maximal matchings in hypergraphs with bounded edges.** The statement that for
every vertex set $V$ and every set $E$ of finite subsets of $V$ such that some natural number $k$
bounds the number of elements of every edge in $E$, the hypergraph with edge set $E$ has a
strongly maximal matching.

This is the claim from the EGRES list of open problems; it has since been refuted. -/
def boundedEdgesStronglyMaximalMatching : Prop :=
  ∀ (V : Type) (E : Set (Finset V)) (k : ℕ), (∀ e ∈ E, e.card ≤ k) →
    ∃ M, IsStronglyMaximal E M

/--
**Bounded edge size does not guarantee a strongly maximal matching.** There are a vertex set
$V$, a set $E$ of finite subsets of $V$ and a natural number $k$ such that every edge in $E$ has
at most $k$ elements, but the hypergraph with edge set $E$ has no strongly maximal matching.

Hollom and Randall Shaw (Theorem 1.2) construct a $3$-uniform (infinite) hypergraph with no
strongly maximal matching, so bounded edge size does not suffice.

Source: EGRES Open
(Egerváry Research Group), list of open problems, Strongly maximal matchings,
https://oldlemon.cs.elte.hu/egres/open/Strongly_maximal_matchings; resolution: L. Hollom and B.
Randall Shaw, Counterexamples to conjectures on strong maximality and minimality, Electron. J.
Combin. 33(2) (2026), P2.11; arXiv:2511.13709, Theorem 1.2: there is a 3-uniform hypergraph H₁ with
no strongly maximal matching (refuting Conjecture 1.1 for matchings and Aharoni's question),
https://doi.org/10.37236/14948.
-/
public theorem_wanted boundedEdgesStronglyMaximalMatching_refuted :
    ¬ boundedEdgesStronglyMaximalMatching

end MathlibExt.Combinatorics.StronglyMaximalMatchingAMR29Problem0084Wanted
