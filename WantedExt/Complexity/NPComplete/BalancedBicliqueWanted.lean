/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BALANCED BICLIQUE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BALANCED COMPLETE
BIPARTITE SUBGRAPH; D. S. Johnson, "The NP-completeness column" (1987).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BalancedBiclique

/-!
# BALANCED BICLIQUE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph contains a complete
bipartite subgraph `K_{K,K}`: two disjoint sets of `K` vertices each, with every cross pair
adjacent. No inducedness is required.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Balanced biclique instances.** An instance of BALANCED BICLIQUE is a triple $(n, es, K)$
consisting of a natural number $n$ (the number of vertices), a list $es$ of pairs of natural
numbers (the edges) and a natural number $K$ (the bound). -/
abbrev BalancedBicliqueInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Graph of a balanced biclique instance.** The graph of a balanced biclique instance
$(n, es, K)$ is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $u$ and $v$
are adjacent when $(u, v)$ or $(v, u)$ belongs to $es$. -/
def Graph (i : BalancedBicliqueInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1


/-- **Well-formed balanced biclique instances.** A balanced biclique instance $(n, es, K)$ is
well formed when the entries of the list $es$ are distinct and every pair $(u, v)$ in $es$
satisfies $u < n$, $v < n$, $u \neq v$ and $(v, u) \notin es$. -/
def WellFormed (i : BalancedBicliqueInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible balanced biclique instances.** A balanced biclique instance $(n, es, K)$ is
feasible when there are disjoint sets $A$ and $B$ of exactly $K$ vertices each in
$\{0, \dots, n-1\}$ such that every vertex of $A$ is adjacent to every vertex of $B$, where
distinct vertices $u$ and $v$ are adjacent when $(u, v)$ or $(v, u)$ belongs to $es$. In other
words, the graph contains a complete bipartite subgraph $K_{K,K}$, not necessarily induced. -/
def BalancedBicliqueFeasible
    (i : BalancedBicliqueInstance) : Prop :=
  ∃ A B : Finset (Fin i.1), A.card = i.2.2 ∧ B.card = i.2.2 ∧ Disjoint A B ∧
    ∀ a ∈ A, ∀ b ∈ B, (Graph i).Adj a b

open Classical in
/-- **The decision problem BALANCED BICLIQUE.** BALANCED BICLIQUE is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
balanced biclique instance $(n, es, K)$ that is well formed (the entries of $es$ are distinct,
and every pair $(u, v)$ in $es$ has $u < n$, $v < n$, $u \neq v$ and $(v, u) \notin es$) and for
which there are disjoint sets $A$ and $B$ of exactly $K$ vertices each in $\{0, \dots, n-1\}$
such that every vertex of $A$ is adjacent to every vertex of $B$, where distinct vertices $u$ and
$v$ are adjacent when $(u, v)$ or $(v, u)$ belongs to $es$. Bitstrings that do not decode are
rejected. -/
noncomputable def balancedBicliqueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BalancedBicliqueInstance) x with
  | some i => decide (WellFormed i ∧ BalancedBicliqueFeasible i)
  | none => false

/-- **BALANCED BICLIQUE is NP-complete.** The decision problem BALANCED BICLIQUE belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), BALANCED COMPLETE BIPARTITE SUBGRAPH; D. S. Johnson, "The NP-
completeness column" (1987). -/
public theorem_wanted balancedBiclique_npComplete :
    balancedBicliqueDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L balancedBicliqueDec

end MetaMathlibExt.Complexity.NPComplete.BalancedBiclique
