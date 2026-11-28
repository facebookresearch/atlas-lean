/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EDGE EMBEDDING ON A GRID: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND47] EDGE EMBEDDING ON A GRID, p. 219,
crediting F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th Conference on
Information Sciences and Systems, Johns Hopkins University, Baltimore (1977), 91-95
(transformation from 3-PARTITION).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EdgeEmbeddingOnAGrid

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, `M`, `N`. -/
abbrev EdgeEmbeddingOnAGridInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EdgeEmbeddingOnAGridInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `M`, `N` are
positive. -/
def WellFormed (i : EdgeEmbeddingOnAGridInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- A one-to-one placement of the vertices on the `M × N` grid in which the two ends of every
edge share a row or a column: `G` is contained in the rook graph on `Fin M × Fin N`. -/
def EdgeEmbeddingOnAGridFeasible (i : EdgeEmbeddingOnAGridInstance) : Prop :=
  (Graph i).IsContained (SimpleGraph.rookGraph i.2.2.1 i.2.2.2)

open Classical in
/-- EDGE EMBEDDING ON A GRID as a decision problem over bitstrings. -/
noncomputable def edgeEmbeddingOnAGridDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeEmbeddingOnAGridInstance) x with
  | some i => decide (WellFormed i ∧ EdgeEmbeddingOnAGridFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EdgeEmbeddingOnAGrid
