/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL BIPARTITE GRAPHS: definitions

Source:
T. Kloks, H. Bodlaender, H. Müller and D. Kratsch, "Computing treewidth and minimum fill-in: all
you need are the minimal separators", Algorithms (ESA '93), Lecture Notes in Computer Science 726
(1993), 260-271, doi:10.1007/3-540-57273-2_61;
Wikipedia, "Pathwidth" (section "Computing path-decompositions"), which records this result.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`,
the graph is bipartite with no induced cycle of length at least `6`, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsBipartite ∧
    (∀ k, 6 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)) ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF CHORDAL BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthChordalBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphs.PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalBipartite
