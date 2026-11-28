/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX DISJOINT CYCLE COVER: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM VERTEX DISJOINT CYCLE COVER;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT13] PARTITION INTO HAMILTONIAN
SUBGRAPHS, comment (the undirected problem with an upper bound `K` on the number of parts);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN
CIRCUIT, the case `K = 1`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.CycleCover

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexDisjointCycleCover

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

end MetaMathlibExt.Complexity.NPComplete.VertexDisjointCycleCover
