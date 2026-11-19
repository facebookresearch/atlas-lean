/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, at most K parts) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO HAMILTONIAN
SUBGRAPHS, comment (p. 193: the undirected problem with `|V_i| ≥ 3` is solvable by matching,
"However, it becomes NP-complete ... if the instance includes an upper bound K on k"), and
problem [GT37] HAMILTONIAN CIRCUIT, the case `K = 1` for nonempty graphs;
R. M. Karp, "Reducibility among combinatorial problems", in R. E. Miller and J. W. Thatcher
(eds.), *Complexity of Computer Computations*, Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (undirected HAMILTONIAN CIRCUIT is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.GroupTheory.Perm.Cycle.Factors

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedBounded

/-!
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, at most K parts) is NP-complete

INSTANCE: an undirected graph `G = (V, E)` and a positive integer `K`. QUESTION: can the
vertices of `G` be partitioned into `k ≤ K` disjoint sets `V₁, ..., Vₖ` such that each `Vᵢ`
contains at least three vertices and induces a subgraph of `G` that contains a Hamiltonian
circuit?

This is the undirected variant of [GT13] (`PartitionIntoHamiltonianSubgraphsWanted`, directed,
no bound on `k`) with the bound `K` added to the instance, as recorded in the entry's comment;
without the bound the undirected problem is solvable in polynomial time by matching
techniques. For `K = 1` and a nonempty graph `G` the question is whether `G` has a Hamiltonian
circuit; the empty graph is a yes-instance for every `K` (zero blocks).

Such a partition is the same thing as a permutation `σ` of `V` with an edge `{v, σ v}` at every
vertex `v`, no cycle of length two (`σ (σ v) ≠ v`; `σ v ≠ v` holds because `G` has no loops),
and at most `K` cycles: given the partition, let `σ v` be the successor of `v` along a
Hamiltonian circuit of its block, oriented either way; conversely, the blocks are the cycles of
`σ`, each has at least three vertices, and following `σ` around a cycle is a Hamiltonian circuit
of the subgraph that cycle induces. Since `σ` fixes no vertex, its cycles are counted by
Mathlib's `Equiv.Perm.cycleFactorsFinset`, the finset of its cycle factors.
`PartitionIntoHamiltonianSubgraphsUndirectedBoundedFeasible` states the question in this
permutation form, as the directed parent does. The graph is a Mathlib `SimpleGraph` given by
an edge list (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PartitionIntoHamiltonianSubgraphsUndirectedBoundedInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoHamiltonianSubgraphsUndirectedBoundedInstance) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : PartitionIntoHamiltonianSubgraphsUndirectedBoundedInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The vertices split into at most `K` blocks of at least three vertices, each inducing a
subgraph with a Hamiltonian circuit: there is a permutation `σ` of the vertices with `v`
adjacent to `σ v` for every vertex `v`, no cycle of length two, and at most `K` cycles. -/
def PartitionIntoHamiltonianSubgraphsUndirectedBoundedFeasible
    (i : PartitionIntoHamiltonianSubgraphsUndirectedBoundedInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1), (∀ v, (Graph i).Adj v (σ v) ∧ σ (σ v) ≠ v) ∧
    σ.cycleFactorsFinset.card ≤ i.2.2

open Classical in
/-- PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, at most K parts) as a decision problem
over bitstrings. -/
noncomputable def partitionIntoHamiltonianSubgraphsUndirectedBoundedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoHamiltonianSubgraphsUndirectedBoundedInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoHamiltonianSubgraphsUndirectedBoundedFeasible i)
  | none => false

/-- **PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete for undirected graphs with a bound
`K` on the number of parts.** Source: Garey and Johnson (1979), [GT13], comment, and [GT37];
Karp (1972). -/
public theorem_wanted partitionIntoHamiltonianSubgraphsUndirectedBounded_npComplete :
    partitionIntoHamiltonianSubgraphsUndirectedBoundedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoHamiltonianSubgraphsUndirectedBoundedDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedBounded
