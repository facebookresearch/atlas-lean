/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, parts of size at least 6) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO HAMILTONIAN
SUBGRAPHS, comment (p. 193: for undirected graphs "it becomes NP-complete if we require that
|V_i| ≥ 6", credited to C. H. Papadimitriou, private communication, 1978);
P. Hell, D. G. Kirkpatrick, J. Kratochvíl and I. Kříž, "On restricted two-factors", SIAM
Journal on Discrete Mathematics 1 (1988), 472-484, doi:10.1137/0401046 (deciding whether a
graph has a two-factor with all cycle lengths in `L` is NP-complete unless every excluded
length is 3 or 4; here the excluded lengths are 3, 4, 5), as recorded by B. Manthey, "On
approximating restricted cycle covers", SIAM Journal on Computing 38 (2008), 181-206,
doi:10.1137/060676003, Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedMinSix

/-!
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, parts of size at least 6) is NP-complete

INSTANCE: an undirected graph `G = (V, E)`. QUESTION: can the vertices of `G` be partitioned
into disjoint sets `V₁, ..., Vₖ`, for some `k`, such that each `Vᵢ` contains at least six
vertices and induces a subgraph of `G` that contains a Hamiltonian circuit?

This is the undirected variant of [GT13] (`PartitionIntoHamiltonianSubgraphsWanted`, directed,
parts of size at least three) recorded in the entry's comment; with parts of size at least
three the undirected problem is solvable in polynomial time by matching techniques.

Such a partition is the same thing as a permutation `σ` of `V` with an edge `{v, σ v}` at every
vertex `v` and no cycle of length at most five (`(σ ^ m) v ≠ v` for `0 < m < 6`): given the
partition, let `σ v` be the successor of `v` along a Hamiltonian circuit of its block, oriented
either way; conversely, the blocks are the cycles of `σ`, each has at least six vertices, and
following `σ` around a cycle is a Hamiltonian circuit of the subgraph that cycle induces. In
other words, the question asks for a two-factor of `G` all of whose cycles have length at least
six. `PartitionIntoHamiltonianSubgraphsUndirectedMinSixFeasible` states the question in the
permutation form, as the directed parent does. The graph is a Mathlib `SimpleGraph` given by an
edge list (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and the edge list. -/
abbrev PartitionIntoHamiltonianSubgraphsUndirectedMinSixInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoHamiltonianSubgraphsUndirectedMinSixInstance) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : PartitionIntoHamiltonianSubgraphsUndirectedMinSixInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The vertices split into blocks of at least six vertices, each inducing a subgraph with a
Hamiltonian circuit: there is a permutation `σ` of the vertices with `v` adjacent to `σ v` for
every vertex `v` and with no cycle of length at most five. -/
def PartitionIntoHamiltonianSubgraphsUndirectedMinSixFeasible
    (i : PartitionIntoHamiltonianSubgraphsUndirectedMinSixInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1), ∀ v, (Graph i).Adj v (σ v) ∧ ∀ m < 6, 0 < m → (σ ^ m) v ≠ v

open Classical in
/-- PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, parts of size at least 6) as a decision
problem over bitstrings. -/
noncomputable def partitionIntoHamiltonianSubgraphsUndirectedMinSixDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoHamiltonianSubgraphsUndirectedMinSixInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoHamiltonianSubgraphsUndirectedMinSixFeasible i)
  | none => false

/-- **PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete for undirected graphs and parts of
size at least 6.** Source: Garey and Johnson (1979), [GT13], comment (Papadimitriou); Hell,
Kirkpatrick, Kratochvíl and Kříž (1988). -/
public theorem_wanted partitionIntoHamiltonianSubgraphsUndirectedMinSix_npComplete :
    partitionIntoHamiltonianSubgraphsUndirectedMinSixDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoHamiltonianSubgraphsUndirectedMinSixDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedMinSix
