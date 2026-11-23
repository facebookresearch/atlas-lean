/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), INDUCED SUBGRAPH
ISOMORPHISM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism

/-!
# INDUCED SUBGRAPH ISOMORPHISM is NP-complete

Two undirected graphs, pattern `H` and host `G`. The question is whether `H` is an induced
subgraph of `G`: an injective map from the vertices of `H` to those of `G` preserving adjacency
in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Induced-subgraph-isomorphism instance.** An instance of INDUCED SUBGRAPH ISOMORPHISM is a
quadruple $(n, E, k, F)$ consisting of a natural number $n$ (the number of host vertices), a list
$E$ of pairs of natural numbers (the host edges), a natural number $k$ (the number of pattern
vertices) and a list $F$ of pairs of natural numbers (the pattern edges). -/
abbrev InducedSubgraphIsomorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)


/-- **Host graph of an induced-subgraph-isomorphism instance.** For an instance $(n, E, k, F)$,
the host graph is the graph of the edge list $E$ on $n$ vertices: the simple graph on
$\{0, \dots, n - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or
$(j, i)$ belongs to $E$. -/
def GraphHost (i : InducedSubgraphIsomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- **Pattern graph of an induced-subgraph-isomorphism instance.** For an instance
$(n, E, k, F)$, the pattern graph is the graph of the edge list $F$ on $k$ vertices: the simple
graph on $\{0, \dots, k - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when $(i, j)$
or $(j, i)$ belongs to $F$. -/
def GraphPattern (i : InducedSubgraphIsomorphismInstance) :
    SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2


/-- **Well-formed induced-subgraph-isomorphism instance.** An instance $(n, E, k, F)$ is
well-formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, and likewise the list $F$ has no repeated
entries and every pair $(u, v)$ in $F$ satisfies $u < k$, $v < k$, $u \ne v$ and
$(v, u) \notin F$. -/
def WellFormed (i : InducedSubgraphIsomorphismInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2

/-- **Induced embedding of the pattern into the host.** An instance $(n, E, k, F)$ is feasible
when there is an injective map $f$ from $\{0, \dots, k - 1\}$ to $\{0, \dots, n - 1\}$ such that,
for all $a, b \in \{0, \dots, k - 1\}$, the vertices $a$ and $b$ are adjacent in the pattern
graph if and only if $f(a)$ and $f(b)$ are adjacent in the host graph. -/
def InducedSubgraphIsomorphismFeasible
    (i : InducedSubgraphIsomorphismInstance) : Prop :=
  ∃ f : Fin i.2.2.1 → Fin i.1, Function.Injective f ∧
    ∀ a b : Fin i.2.2.1,
      (GraphPattern i).Adj a b ↔ (GraphHost i).Adj (f a) (f b)

open Classical in
/-- **INDUCED SUBGRAPH ISOMORPHISM as a decision problem.** The decision problem INDUCED SUBGRAPH
ISOMORPHISM accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance $(n, E, k, F)$ (host vertex count, host edge list, pattern vertex count,
pattern edge list) that is well-formed and for which there is an injective map $f$ from
$\{0, \dots, k - 1\}$ to $\{0, \dots, n - 1\}$ such that, for all $a$ and $b$, the vertices $a$
and $b$ are adjacent in the pattern graph if and only if $f(a)$ and $f(b)$ are adjacent in the
host graph. Bitstrings that do not decode to an instance are rejected. -/
noncomputable def inducedSubgraphIsomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedSubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ InducedSubgraphIsomorphismFeasible i)
  | none => false

/-- **INDUCED SUBGRAPH ISOMORPHISM is NP-complete.** The decision problem INDUCED SUBGRAPH
ISOMORPHISM is in NP, and every decision problem in NP reduces to it by a polynomial-time
many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), INDUCED SUBGRAPH ISOMORPHISM. -/
public theorem_wanted inducedSubgraphIsomorphism_npComplete :
    inducedSubgraphIsomorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inducedSubgraphIsomorphismDec

end MetaMathlibExt.Complexity.NPComplete.InducedSubgraphIsomorphism
