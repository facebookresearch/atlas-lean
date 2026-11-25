/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CIRCLE GRAPHS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthCircleGraphs

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph PathwidthChordalGraphsFeasible)

/-!
# PATHWIDTH OF CIRCLE GRAPHS is NP-complete

INSTANCE: a circle graph `G = (V, E)` (the intersection graph of a family of chords of a circle)
and a positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`?

Kloks, Bodlaender, Müller, and Kratsch prove that PATHWIDTH is NP-complete on bipartite
distance-hereditary graphs; distance-hereditary graphs are circle graphs, so it is NP-complete on
circle graphs, as Mihai and Todinca record. Membership in NP: a path decomposition (and a chord
model) is a polynomial certificate.

The graph is given by its vertex count and edge list. It is a circle graph when it is isomorphic
to the circle graph of a chord model in the sense of `DominatingSetCircleGraphWanted`: chords
`(a, b)` with `a < b`, all endpoints distinct, two chords adjacent when their endpoints interleave
(`DominatingSetCircleGraph.circleGraph`).

A path decomposition of `G` is a sequence of bags `X 0, …, X (r - 1)` of vertices such that every
vertex lies in some bag, both ends of every edge lie in a common bag, and the bags containing any
one vertex are consecutive; the pathwidth of `G` is at most `K` exactly when some path decomposition
has all bags of size at most `K + 1`. The instance type, the graph, the path decompositions and the
question are reused from `PathwidthChordalGraphsWanted`
(`PathwidthChordalGraphs.PathwidthChordalGraphsInstance`, `PathwidthChordalGraphs.Graph`,
`PathwidthChordalGraphs.IsPathDecomposition`,
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`, which says only that the pathwidth is at
most `K`); this module replaces chordality by its own graph class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PATHWIDTH OF CIRCLE GRAPHS is NP-complete.** Source: Kloks, Bodlaender, Müller, and Kratsch
(1993); Mihai and Todinca (2009). -/
public theorem_wanted pathwidthCircleGraphs_npComplete :
    pathwidthCircleGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthCircleGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthCircleGraphs
