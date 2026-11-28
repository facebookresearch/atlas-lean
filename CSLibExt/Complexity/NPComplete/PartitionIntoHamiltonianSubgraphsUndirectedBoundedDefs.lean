/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO HAMILTONIAN SUBGRAPHS (undirected, at most K parts): definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.GroupTheory.Perm.Cycle.Factors

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedBounded

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

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoHamiltonianSubgraphsUndirectedBounded
