/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM COMMON INDUCED
SUBGRAPH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph

/-!
# MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete

Two undirected graphs and a bound `K`. The question is whether they have a common induced
subgraph on at least `K` vertices: subsets of vertices of the two graphs and a bijection
between them preserving adjacency in both directions.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MAXIMUM COMMON INDUCED SUBGRAPH.** An instance of MAXIMUM COMMON INDUCED
SUBGRAPH is a tuple $(n_1, E_1, n_2, E_2, K)$ in which $n_1$, $n_2$ and $K$ are natural numbers
and $E_1$, $E_2$ are finite lists of pairs of natural numbers: $n_1$ is the vertex count of the
first graph, $E_1$ its edge list, $n_2$ the vertex count of the second graph, $E_2$ its edge
list, and $K$ the bound. -/
abbrev MaximumCommonInducedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ


/-- **First graph of an instance.** For an instance $(n_1, E_1, n_2, E_2, K)$ of MAXIMUM COMMON
INDUCED SUBGRAPH, the first graph is the graph of the edge list $E_1$ on $n_1$ vertices: the
simple graph on $\{0, \dots, n_1 - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when
$(i, j)$ or $(j, i)$ belongs to $E_1$. -/
def GraphFirst (i : MaximumCommonInducedSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- **Second graph of an instance.** For an instance $(n_1, E_1, n_2, E_2, K)$ of MAXIMUM COMMON
INDUCED SUBGRAPH, the second graph is the graph of the edge list $E_2$ on $n_2$ vertices: the
simple graph on $\{0, \dots, n_2 - 1\}$ in which distinct vertices $i$ and $j$ are adjacent when
$(i, j)$ or $(j, i)$ belongs to $E_2$. -/
def GraphSecond (i : MaximumCommonInducedSubgraphInstance) :
    SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2.1


/-- **Well-formed instances of MAXIMUM COMMON INDUCED SUBGRAPH.** An instance
$(n_1, E_1, n_2, E_2, K)$ of MAXIMUM COMMON INDUCED SUBGRAPH is well formed when, for each
$k \in \{1, 2\}$, the list $E_k$ has no repeated entries and every pair $(u, v)$ in $E_k$ has
$u < n_k$, $v < n_k$, $u \ne v$ and $(v, u) \notin E_k$. -/
def WellFormed (i : MaximumCommonInducedSubgraphInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.2.1.Nodup ∧
    ∀ e ∈ i.2.2.2.1, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1

/-- **Feasible instances of MAXIMUM COMMON INDUCED SUBGRAPH.** An instance
$(n_1, E_1, n_2, E_2, K)$ of MAXIMUM COMMON INDUCED SUBGRAPH is feasible when, writing $G_1$ and
$G_2$ for its first and second graphs, there are a set $A$ of vertices of $G_1$ and a set $B$ of
vertices of $G_2$ with $|A| \ge K$ and $|B| = |A|$, and a bijection $f : A \to B$ such that for
all $a, b \in A$, the vertices $a$ and $b$ are adjacent in $G_1$ if and only if $f(a)$ and $f(b)$
are adjacent in $G_2$. -/
def MaximumCommonInducedSubgraphFeasible
    (i : MaximumCommonInducedSubgraphInstance) : Prop :=
  ∃ A : Finset (Fin i.1), ∃ B : Finset (Fin i.2.2.1),
    i.2.2.2.2 ≤ A.card ∧ B.card = A.card ∧
    ∃ f : ↥A → ↥B, Function.Bijective f ∧
      ∀ a b : ↥A,
        (GraphFirst i).Adj (a : Fin i.1) (b : Fin i.1) ↔
          (GraphSecond i).Adj (f a : Fin i.2.2.1) (f b : Fin i.2.2.1)

open Classical in
/-- **MAXIMUM COMMON INDUCED SUBGRAPH as a decision problem.** The decision problem MAXIMUM
COMMON INDUCED SUBGRAPH accepts a bitstring $x$ exactly when the canonical bitstring decoding of
$x$ yields an instance of MAXIMUM COMMON INDUCED SUBGRAPH that is well formed and feasible.
Bitstrings that do not decode to an instance are rejected. -/
noncomputable def maximumCommonInducedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumCommonInducedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ MaximumCommonInducedSubgraphFeasible i)
  | none => false

/-- **MAXIMUM COMMON INDUCED SUBGRAPH is NP-complete.** The decision problem MAXIMUM COMMON
INDUCED SUBGRAPH belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MAXIMUM COMMON INDUCED SUBGRAPH. -/
public theorem_wanted maximumCommonInducedSubgraph_npComplete :
    maximumCommonInducedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCommonInducedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCommonInducedSubgraph
