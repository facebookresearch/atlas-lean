/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CIRCLE GRAPHS: definitions

Source:
T. Kloks, H. L. Bodlaender, H. Müller, and D. Kratsch, "Computing treewidth and minimum fill-in:
all you need are the minimal separators", Algorithms - ESA '93, Lecture Notes in Computer Science
726 (1993), 260-271, doi:10.1007/3-540-57273-2_61 (pathwidth is NP-complete on bipartite
distance-hereditary graphs);
D. Mihai and I. Todinca, "Pathwidth is NP-hard for weighted trees", Frontiers in Algorithmics
(FAW 2009), Lecture Notes in Computer Science 5598 (2009), 181-195,
doi:10.1007/978-3-642-02270-8_20 (records that pathwidth remains NP-hard for distance-hereditary
graphs and circle graphs, and that circle graphs contain all distance-hereditary graphs).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.DominatingSetCircleGraphDefs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthCircleGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-- `G` is a circle graph: it is isomorphic to the circle graph of a chord model whose chords
`(a, b)` satisfy `a < b` and have pairwise distinct endpoints. -/
def IsCircleGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ C : List (ℕ × ℕ), (∀ c ∈ C, c.1 < c.2) ∧ (C.flatMap fun c => [c.1, c.2]).Nodup ∧
    Nonempty (G ≃g DominatingSetCircleGraph.circleGraph C)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is a circle
graph, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsCircleGraph (Graph i) ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF CIRCLE GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthCircleGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthCircleGraphs
