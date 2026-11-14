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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Equiv.Defs

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

/-- An instance: vertex count `n` (vertices `Fin n`) and the arc list; a pair `(u, v)` is the
arc `u → v`. -/
abbrev PartitionIntoHamiltonianSubgraphsInstance := ℕ × List (ℕ × ℕ)

/-- The directed graph of the instance, with an arc `u → v` for each pair `(u, v)` of the arc
list. -/
def Graph (i : PartitionIntoHamiltonianSubgraphsInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Well-formedness of an instance: no repeated arcs, endpoints in range, and no loops.
Opposite arcs `u → v` and `v → u` may both occur. -/
def WellFormed (i : PartitionIntoHamiltonianSubgraphsInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- The vertices split into blocks of at least three vertices, each inducing a subgraph with a
directed Hamiltonian circuit: there is a permutation `σ` of the vertices with an arc from every
vertex `v` to `σ v` and with no cycles of length one or two. -/
def PartitionIntoHamiltonianSubgraphsFeasible
    (i : PartitionIntoHamiltonianSubgraphsInstance) : Prop :=
  ∃ σ : Equiv.Perm (Fin i.1), ∀ v, (Graph i).Adj v (σ v) ∧ σ v ≠ v ∧ σ (σ v) ≠ v

open Classical in
/-- PARTITION INTO HAMILTONIAN SUBGRAPHS as a decision problem over bitstrings. -/
noncomputable def partitionIntoHamiltonianSubgraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoHamiltonianSubgraphsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoHamiltonianSubgraphsFeasible i)
  | none => false

/-- **PARTITION INTO HAMILTONIAN SUBGRAPHS is NP-complete.** Source: Garey and Johnson (1979),
[GT13] (Valiant, unpublished); Manthey (2008). -/
public theorem_wanted partitionIntoHamiltonianSubgraphs_npComplete :
    partitionIntoHamiltonianSubgraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partitionIntoHamiltonianSubgraphsDec

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphs
