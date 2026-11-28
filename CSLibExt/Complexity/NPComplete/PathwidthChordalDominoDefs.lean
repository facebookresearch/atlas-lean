/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL DOMINOES: definitions

Source:
T. Kloks, D. Kratsch and H. Müller, "Dominoes", Graph-Theoretic Concepts in Computer Science
(WG '94), Lecture Notes in Computer Science 903 (1995), 106-120, doi:10.1007/3-540-59071-4_41;
technical report version: Computing Science Note 94/12, Eindhoven University of Technology
(1994).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalDomino

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-- Well-formedness of an instance: a well-formed instance of `PathwidthChordalGraphsWanted` (a
simple edge list, a chordal graph, `0 < K`) in which every vertex lies in at most two maximal
cliques. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  PathwidthChordalGraphs.WellFormed i ∧
    ∀ v : Fin i.1, {s : Set (Fin i.1) | Maximal (Graph i).IsClique s ∧ v ∈ s}.ncard ≤ 2

open Classical in
/-- PATHWIDTH OF CHORDAL DOMINOES as a decision problem over bitstrings. -/
noncomputable def pathwidthChordalDominoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphs.PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalDomino
