/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LEAF SPANNING TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM LEAF SPANNING
TREE.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree

/-!
# MAXIMUM LEAF SPANNING TREE is NP-complete

An undirected graph and a bound `K`. The question is whether the graph has a spanning tree with
at least `K` leaves. A connected edge set with `n - 1` edges is a tree, so acyclicity need not
be stated separately; the leaf count is witnessed by a list of at least `K` vertices each
incident with exactly one tree edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **Instances of MAXIMUM LEAF SPANNING TREE.** An instance of MAXIMUM LEAF SPANNING TREE is a
triple $(n, es, K)$ of a natural number $n$ (the number of vertices), a list $es$ of pairs of
natural numbers (the edge list) and a natural number $K$ (the bound on the number of leaves). -/
abbrev MaximumLeafSpanningTreeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- **Well-formed MAXIMUM LEAF SPANNING TREE instances.** An instance $(n, es, K)$ of MAXIMUM LEAF
SPANNING TREE is well formed when $n > 0$, the list $es$ has no repeated entries, and every entry
$(u, v)$ of $es$ satisfies $u < n$, $v < n$ and $u \ne v$, and $(v, u)$ is not an entry of
$es$. -/
def WellFormed (i : MaximumLeafSpanningTreeInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- **Feasible MAXIMUM LEAF SPANNING TREE instances.** An instance $(n, es, K)$ of MAXIMUM LEAF
SPANNING TREE is feasible when there are a sublist $T$ of $es$ (a list obtained from $es$ by
deleting entries) with no repeated entries and exactly $n - 1$ entries, and a set $L$ of at least
$K$ vertices in $\{0, \dots, n - 1\}$, such that the simple graph on $\{0, \dots, n - 1\}$ in
which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ is an entry of $T$ is
connected, and each vertex in $L$ is an endpoint of exactly one entry of $T$. -/
def MaximumLeafSpanningTreeFeasible
    (i : MaximumLeafSpanningTreeInstance) : Prop :=
  ∃ T : List (ℕ × ℕ), T.Sublist i.2.1 ∧ T.Nodup ∧ T.length = i.1 - 1 ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 T).Connected ∧
    ∃ leaves : Finset (Fin i.1), i.2.2 ≤ leaves.card ∧
      ∀ v ∈ leaves, ∃! e ∈ T, e.1 = (v : ℕ) ∨ e.2 = (v : ℕ)

open Classical in
/-- **The decision problem MAXIMUM LEAF SPANNING TREE.** The decision problem MAXIMUM LEAF
SPANNING TREE accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding of instances, to an instance $(n, es, K)$ of MAXIMUM LEAF SPANNING TREE that is well
formed and feasible (its graph has a spanning tree with at least $K$ leaves). Bitstrings that do
not decode are rejected. -/
noncomputable def maximumLeafSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLeafSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLeafSpanningTreeFeasible i)
  | none => false

/-- **MAXIMUM LEAF SPANNING TREE is NP-complete.** The decision problem MAXIMUM LEAF SPANNING TREE
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MAXIMUM LEAF SPANNING TREE. -/
public theorem_wanted maximumLeafSpanningTree_npComplete :
    maximumLeafSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLeafSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree
