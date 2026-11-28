/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LARGEST COMMON SUBGRAPH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT49] LARGEST
COMMON SUBGRAPH (transformation from CLIQUE; no other reference given there).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph

/-- An instance: vertex count `n₁` of `G` (vertices `Fin n₁`), edge list of `G`, vertex count
`n₂` of `H` (vertices `Fin n₂`), edge list of `H`, and the bound `K`. -/
abbrev LargestCommonSubgraphInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ) × ℕ

/-- The first graph `G = (V₁, E₁)` as a `SimpleGraph (Fin n₁)`. -/
def GraphG (i : LargestCommonSubgraphInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The second graph `H = (V₂, E₂)` as a `SimpleGraph (Fin n₂)`. -/
def GraphH (i : LargestCommonSubgraphInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2.1

/-- Well-formedness of an instance: both edge lists describe simple graphs (no duplicate edges
in either orientation, no self-loops, endpoints in range), and `K` is positive. -/
def WellFormed (i : LargestCommonSubgraphInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.1.Nodup ∧
      ∀ e ∈ i.2.2.2.1, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2.1) ∧
    0 < i.2.2.2.2

/-- Spanning subgraphs `G' ≤ G` and `H' ≤ H` with the same number of edges, at least `K`, that
are isomorphic. -/
def LargestCommonSubgraphFeasible (i : LargestCommonSubgraphInstance) : Prop :=
  ∃ G' : SimpleGraph (Fin i.1), ∃ H' : SimpleGraph (Fin i.2.2.1),
    G' ≤ GraphG i ∧ H' ≤ GraphH i ∧
      G'.edgeSet.ncard = H'.edgeSet.ncard ∧ i.2.2.2.2 ≤ G'.edgeSet.ncard ∧
        Nonempty (G' ≃g H')

open Classical in
/-- LARGEST COMMON SUBGRAPH as a decision problem over bitstrings. -/
noncomputable def largestCommonSubgraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LargestCommonSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ LargestCommonSubgraphFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LargestCommonSubgraph
