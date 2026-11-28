/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUBIC SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT32] CUBIC SUBGRAPH (credited
there to V. Chvátal, 1976); I. A. Stewart, "Deciding whether a planar graph has a cubic
subgraph is NP-complete", Discrete Mathematics 126 (1994), 349-357,
doi:10.1016/0012-365X(94)90277-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicSubgraph

/-- An instance: vertex count `n` (vertices `Fin n`), edge list. -/
abbrev CubicSubgraphInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CubicSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CubicSubgraphInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

open Classical in
/-- Some spanning subgraph `H ≤ G` has at least one edge, and every vertex has degree 0 or 3
in `H`. -/
def CubicSubgraphFeasible (i : CubicSubgraphInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), H ≤ Graph i ∧ H.edgeSet.Nonempty ∧
    ∀ v, H.degree v = 0 ∨ H.degree v = 3

open Classical in
/-- CUBIC SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def cubicSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CubicSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ CubicSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CubicSubgraph
