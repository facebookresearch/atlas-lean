/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET in tournaments is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetDirectedDegreeTwoWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTournaments

open FeedbackVertexSetDirectedDegreeTwo (FeedbackVertexSetDirectedInstance SimpleArcs
  FeedbackVertexSetDirectedFeasible)

/-!
# FEEDBACK VERTEX SET in tournaments is NP-complete

INSTANCE: a tournament `T = (V, A)`, i.e. a directed graph with exactly one arc between every two
distinct vertices (an orientation of the complete graph), and a positive integer `K ≤ |V|`.
QUESTION: is there a subset `V' ⊆ V` with `|V'| ≤ K` such that `V'` contains at least one vertex
from every directed cycle in `T`?

This is FEEDBACK VERTEX SET ([GT7]) restricted to tournaments. The instance type (vertex count,
arc list, bound), the digraph conditions `SimpleArcs` (no loops or repeated arcs, endpoints
below `n`) and the question `FeedbackVertexSetDirectedFeasible` (a `Finset` of at most `K`
vertices meeting every closed directed walk of positive length, equivalently every directed
cycle) are those of `FeedbackVertexSetDirectedDegreeTwoWanted`, reused unchanged without its
degree bound. The restriction adds that the digraph is a tournament (`IsTournament`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FEEDBACK VERTEX SET is NP-complete on tournaments.** Source: Garey and Johnson (1979),
[GT7]; Speckenmeyer (1990); Mnich, Vassilevska Williams and Végh (2015). -/
public theorem_wanted feedbackVertexSetTournaments_npComplete :
    feedbackVertexSetTournamentsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetTournamentsDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetTournaments
