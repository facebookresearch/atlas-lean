/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET in tournaments: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
E. Speckenmeyer, "On feedback problems in digraphs", in *Graph-Theoretic Concepts in Computer
Science (WG '89)*, Lecture Notes in Computer Science 411, Springer (1990), 218-231,
doi:10.1007/3-540-52292-1_16 (reduction from VERTEX COVER to FEEDBACK VERTEX SET in tournaments);
recorded in M. Mnich, V. Vassilevska Williams and L. A. Végh, "A 7/3-approximation for feedback
vertex sets in tournaments", arXiv:1511.01137 (2015), Section 1 ("The Feedback Vertex Set problem
remains NP-complete and APX-hard in tournaments").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTournaments

open FeedbackVertexSetDirectedDegreeTwo (FeedbackVertexSetDirectedInstance SimpleArcs
  FeedbackVertexSetDirectedFeasible)

/-- The digraph is a tournament: for every two distinct vertices `u ≠ v` below `n`, exactly one
of the arcs `u → v` and `v → u` is listed. -/
def IsTournament (i : FeedbackVertexSetDirectedInstance) : Prop :=
  ∀ u < i.1, ∀ v < i.1, u ≠ v → ((u, v) ∈ i.2.1 ↔ (v, u) ∉ i.2.1)

/-- Well-formedness of an instance: the arc list is a digraph without loops or repeated arcs,
the digraph is a tournament, and `0 < K ≤ |V|`. -/
def WellFormed (i : FeedbackVertexSetDirectedInstance) : Prop :=
  SimpleArcs i ∧ IsTournament i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- FEEDBACK VERTEX SET in tournaments as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetTournamentsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetDirectedInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetDirectedFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTournaments
