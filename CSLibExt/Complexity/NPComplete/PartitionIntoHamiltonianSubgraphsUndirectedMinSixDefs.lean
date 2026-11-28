/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, parts of size at least 6): definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedMinSix

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

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedMinSix
