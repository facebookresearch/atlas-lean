/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL BIPARTITE GRAPHS is NP-complete

Source:
T. Kloks, H. Bodlaender, H. Müller and D. Kratsch, "Computing treewidth and minimum fill-in: all
you need are the minimal separators", Algorithms (ESA '93), Lecture Notes in Computer Science 726
(1993), 260-271, doi:10.1007/3-540-57273-2_61;
Wikipedia, "Pathwidth" (section "Computing path-decompositions"), which records this result.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalBipartite

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-!
# PATHWIDTH OF CHORDAL BIPARTITE GRAPHS is NP-complete

INSTANCE: a chordal bipartite graph `G = (V, E)` (bipartite, and every cycle of length at least
6 has a chord) and a positive integer `K`.
QUESTION: is the pathwidth of `G` at most `K`?

This is PATHWIDTH restricted to chordal bipartite graphs, encoded as in the merged
`ChordalBipartiteHamiltonianCircuitWanted`: bipartite (Mathlib's `SimpleGraph.IsBipartite`) with no
induced cycle of length at least 6 (`SimpleGraph.cycleGraph k` with `IsIndContained`), which is
the same as every cycle of length at least 6 having a chord. Kloks, Bodlaender, Müller and Kratsch
show that PATHWIDTH is NP-complete on bipartite distance-hereditary graphs; these are chordal
bipartite, so PATHWIDTH stays NP-complete on chordal bipartite graphs (Wikipedia, "Pathwidth",
records both statements with this citation). Membership in NP is immediate.

The instance, the graph and the question are those of the merged
`PathwidthChordalGraphsWanted`, reused unchanged: vertex count, edge list on `Fin n` and bound
`K` (`PathwidthChordalGraphsInstance`, `PathwidthChordalGraphs.Graph`), and the question
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`: some path decomposition (bags
`X 0, …, X (r - 1)` covering every vertex and every edge, each vertex in a contiguous run of
bags, `PathwidthChordalGraphs.IsPathDecomposition`) has every bag of size at most `K + 1`. That
question does not mention chordality. Well-formedness is the parent's simple-edge-list condition
and `0 < K` (as in the parent, the source's "positive integer k"), with the class restriction in
place of chordality.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PATHWIDTH OF CHORDAL BIPARTITE GRAPHS is NP-complete.**
Source: Kloks, Bodlaender, Müller and Kratsch (1993). -/
public theorem_wanted pathwidthChordalBipartite_npComplete :
    pathwidthChordalBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthChordalBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalBipartite
