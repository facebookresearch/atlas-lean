/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL DOMINOES is NP-complete

Source:
T. Kloks, D. Kratsch and H. Müller, "Dominoes", Graph-Theoretic Concepts in Computer Science
(WG '94), Lecture Notes in Computer Science 903 (1995), 106-120, doi:10.1007/3-540-59071-4_41;
technical report version: Computing Science Note 94/12, Eindhoven University of Technology
(1994).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalDomino

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-!
# PATHWIDTH OF CHORDAL DOMINOES is NP-complete

INSTANCE: a chordal domino `G = (V, E)`, that is, a chordal graph in which every vertex belongs
to at most two maximal cliques, and a positive integer `K`.
QUESTION: is the pathwidth of `G` at most `K`?

This is PATHWIDTH restricted to chordal dominoes. Kloks, Kratsch and Müller (Definition 1):
"A graph is called a domino if every vertex occurs in at most two maximal cliques"; they show
that PATHWIDTH ("Given a graph G and a positive integer k, decide whether the pathwidth of G is at
most k") remains NP-complete when restricted to chordal dominoes. Chordality is encoded as in
`PathwidthChordalGraphs.WellFormed` (no induced cycle of length at least 4). A maximal clique is a
vertex set `s` with Mathlib's `Maximal G.IsClique s` (a clique contained in no larger clique), and
the domino condition bounds by 2 the number (`Set.ncard`) of maximal cliques containing each
vertex.

The instance, the graph and the question are those of the merged
`PathwidthChordalGraphsWanted`, reused unchanged: vertex count, edge list on `Fin n` and bound
`K` (`PathwidthChordalGraphsInstance`, `PathwidthChordalGraphs.Graph`), and the question
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`: some path decomposition (bags
`X 0, …, X (r - 1)` covering every vertex and every edge, each vertex in a contiguous run of
bags, `PathwidthChordalGraphs.IsPathDecomposition`) has every bag of size at most `K + 1`. That
question does not mention chordality. Well-formedness is the parent's
`PathwidthChordalGraphs.WellFormed` (simple edge list, chordal, `0 < K`, the source's "positive
integer k") plus the domino condition.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PATHWIDTH OF CHORDAL DOMINOES is NP-complete.**
Source: Kloks, Kratsch and Müller (1995). -/
public theorem_wanted pathwidthChordalDomino_npComplete :
    pathwidthChordalDominoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthChordalDominoDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalDomino
