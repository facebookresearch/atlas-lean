/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH GRAPH COMPLETION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT36] PATH GRAPH COMPLETION, p. 199
(reference: [Gavril, 1977b], listed in Garey and Johnson's bibliography as F. Gavril, private
communication; transformation from INTERVAL GRAPH COMPLETION). The original was not available;
Garey and Johnson's entry records the result and its attribution.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathGraphCompletion

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PathGraphCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PathGraphCompletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range); `K ≥ 0` needs no
condition. -/
def WellFormed (i : PathGraphCompletionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- Some undirected path graph `H` on the same vertices contains the graph and has at most `K`
edges that are not edges of the graph. -/
def PathGraphCompletionFeasible (i : PathGraphCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Graph i ≤ H ∧
    (H.edgeSet \ (Graph i).edgeSet).ncard ≤ i.2.2 ∧
      DominatingSetUndirectedPathGraphs.IsUndirectedPathGraph H

open Classical in
/-- PATH GRAPH COMPLETION as a decision problem over bitstrings. -/
noncomputable def pathGraphCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PathGraphCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathGraphCompletion
