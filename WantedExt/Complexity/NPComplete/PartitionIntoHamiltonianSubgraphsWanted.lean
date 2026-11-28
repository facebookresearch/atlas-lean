/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO
HAMILTONIAN SUBGRAPHS (credited there to L. G. Valiant, unpublished);
B. Manthey, "On approximating restricted cycle covers", SIAM Journal on
Computing 38 (2008), 181-206, doi:10.1137/060676003 (Section 1: deciding
whether a directed graph has a cycle cover all of whose cycles have length at
least three is NP-complete, citing Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphs

/-!
# PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete

INSTANCE: a directed graph `G = (V, A)`. QUESTION: can the vertices of `G` be partitioned into
disjoint sets `V₁, ..., Vₖ`, for some `k`, such that each `Vᵢ` contains at least three vertices
and induces a subgraph of `G` that contains a (directed) Hamiltonian circuit?

Such a partition is the same thing as a permutation `σ` of `V` with an arc `v → σ v` at every
vertex `v` and no cycle of length one or two (`σ v ≠ v` and `σ (σ v) ≠ v`): given the partition,
let `σ v` be the successor of `v` on the Hamiltonian circuit of its block; conversely, the blocks
are the cycles of `σ`, each has at least three vertices, and following `σ` around a cycle is a
Hamiltonian circuit of the subgraph that cycle induces. `PartitionIntoHamiltonianSubgraphsFeasible`
states the question in this permutation form. The directed graph is Mathlib's `Digraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT13] (Valiant, unpublished); Manthey (2008). -/
public theorem_wanted partitionIntoHamiltonianSubgraphs_npComplete :
    partitionIntoHamiltonianSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoHamiltonianSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphs
