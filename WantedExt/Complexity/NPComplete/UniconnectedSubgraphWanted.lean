/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNICONNECTED SUBGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT30] UNICONNECTED SUBGRAPH;
S. N. Maheshwari, "Traversal marker placement problems are NP-complete", Technical Report
CU-CS-092-76, Department of Computer Science, University of Colorado, Boulder (1976),
Lemma 1, https://scholar.colorado.edu/concern/reports/rb68xc64n.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Batteries.Data.List.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraph

/-!
# UNICONNECTED SUBGRAPH is NP-complete

INSTANCE: a directed graph `G = (V, A)` (no loops, no multiple arcs) and a positive integer
`K ≤ |A|`. QUESTION: is there a subset `A' ⊆ A` with `|A'| ≥ K` such that `G' = (V, A')` has
at most one directed path between any pair of vertices?

The subset `A'` is a subdigraph `H ≤ G` (Mathlib's `Digraph` order) and `|A'|` is the number of
ordered pairs `(u, v)` with `H.Adj u v`. A directed path is a nonempty list of distinct
vertices, each joined to the next by an arc (`IsDirectedPath`); "at most one directed path
between any pair" says that two directed paths with the same first and the same last vertex
are equal. For a pair `(u, u)` the only directed path is `[u]`, so directed cycles are allowed.
Under `WellFormed` the arc list has one entry per arc, so its length is `|A|`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), arc list (ordered pairs), bound `K`. -/
abbrev UniconnectedSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph of the instance: `u → v` is an arc iff `(u, v)` is in the arc list. -/
def Graph (i : UniconnectedSubgraphInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no
duplicate arcs, no loops, endpoints in range; opposite arcs `(u, v)` and `(v, u)` are allowed),
and `0 < K ≤ |A|`, the length of the arc list. -/
def WellFormed (i : UniconnectedSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- `p` is a directed path of `H`: a nonempty list of distinct vertices in which each vertex is
joined to the next one by an arc of `H`. -/
def IsDirectedPath {V : Type*} (H : Digraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain H.Adj

/-- Some subdigraph `H ≤ G` on the same vertices has at least `K` arcs and at most one directed
path from any vertex to any vertex. -/
def UniconnectedSubgraphFeasible (i : UniconnectedSubgraphInstance) : Prop :=
  ∃ H : Digraph (Fin i.1), H ≤ Graph i ∧
    i.2.2 ≤ {a : Fin i.1 × Fin i.1 | H.Adj a.1 a.2}.ncard ∧
    ∀ p q : List (Fin i.1), IsDirectedPath H p → IsDirectedPath H q →
      p.head? = q.head? → p.getLast? = q.getLast? → p = q

open Classical in
/-- UNICONNECTED SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def uniconnectedSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniconnectedSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ UniconnectedSubgraphFeasible i)
  | none => false

/-- **UNICONNECTED SUBGRAPH is NP-complete.** Source: Garey and Johnson (1979), [GT30];
Maheshwari (1976). -/
public theorem_wanted uniconnectedSubgraph_npComplete :
    uniconnectedSubgraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L uniconnectedSubgraphDec

end MetaMathlibExt.Complexity.NPComplete.UniconnectedSubgraph
