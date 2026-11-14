/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX DISJOINT CYCLE COVER is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem [GT21] MINIMUM VERTEX DISJOINT CYCLE COVER;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO HAMILTONIAN
SUBGRAPHS, comment (the undirected problem with an upper bound `K` on the number of parts);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN
CIRCUIT, the case `K = 1`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.CycleCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexDisjointCycleCover

/-!
# VERTEX DISJOINT CYCLE COVER is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`. QUESTION: is there a family `F` of
vertex disjoint cycles covering `V` with at most `K` cycles?

This is the decision version, with bound `K`, of Crescenzi and Kann's [GT21] MINIMUM VERTEX
DISJOINT CYCLE COVER ("A family `F` of vertex disjoint cycles covering `V`", measure "Number of
cycles in `F`"). Equivalently, `V` is partitioned into at most `K` sets, each with at least three
vertices and inducing a subgraph that contains a Hamiltonian circuit: Garey and Johnson's [GT13]
comment records that this undirected problem "becomes NP-complete … if the instance includes an
upper bound `K` on `k`". For a graph with at least one vertex, the case `K = 1` asks for a single
cycle through every vertex, which is HAMILTONIAN CIRCUIT (Karp 1972); so HAMILTONIAN CIRCUIT
reduces to this problem by mapping a graph `G` with a vertex to `(G, 1)` and the empty graph (no
Hamiltonian circuit) to a fixed no-instance, such as a single edge with `K = 1`. The empty graph
itself is a yes-instance here for every `K`: it is covered by the empty family (`k = 0`). It is
in NP: the cycles are a certificate. The vertex count `n` is binary, but a vertex on no edge lies
on no cycle, so an instance with more than `2|E|` vertices is a no-instance, recognized in
polynomial time, and otherwise the certificate lists at most `n ≤ 2|E|` vertices.

The graph is given by an edge list on `Fin n`. A cycle is a `SimpleGraph.Cycle` (from
`MathlibExt.Combinatorics.SimpleGraph.CycleCover`): a base vertex and a closed walk at it with
Mathlib's `SimpleGraph.Walk.IsCycle` (nonempty, no repeated edge, no repeated vertex except the
endpoints; in a simple graph it has length at least `3`). The family is indexed by `Fin k` with
`k ≤ K`, and "vertex disjoint, covering `V`" says that every vertex lies on exactly one of the
cycles, i.e. in the support of exactly one of their walks.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev VertexDisjointCycleCoverInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : VertexDisjointCycleCoverInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate
edges in either orientation, no self-loops, endpoints in range), and `K` is positive. -/
def WellFormed (i : VertexDisjointCycleCoverInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- Some family of `k ≤ K` cycles `c j` of `G` covers every vertex exactly once: each vertex
lies on exactly one of the cycles. -/
def VertexDisjointCycleCoverFeasible (i : VertexDisjointCycleCoverInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin k → SimpleGraph.Cycle (Graph i), ∀ v, ∃! j, v ∈ (c j).walk.support

open Classical in
/-- VERTEX DISJOINT CYCLE COVER as a decision problem over bitstrings. -/
noncomputable def vertexDisjointCycleCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := VertexDisjointCycleCoverInstance) x with
  | some i => decide (WellFormed i ∧ VertexDisjointCycleCoverFeasible i)
  | none => false

/-- **VERTEX DISJOINT CYCLE COVER is NP-complete.** Source: Crescenzi and Kann (2000), [GT21];
Garey and Johnson (1979), [GT13], comment; Karp (1972). -/
public theorem_wanted vertexDisjointCycleCover_npComplete :
    vertexDisjointCycleCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vertexDisjointCycleCoverDec

end MetaMathlibExt.Complexity.NPComplete.VertexDisjointCycleCover
