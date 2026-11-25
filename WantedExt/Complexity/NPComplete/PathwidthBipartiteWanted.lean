/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF BIPARTITE GRAPHS is NP-complete

Source:
T. Kloks, H. Bodlaender, H. Müller and D. Kratsch, "Computing treewidth and minimum fill-in: all
you need are the minimal separators", Algorithms (ESA '93), Lecture Notes in Computer Science 726
(1993), 260-271, doi:10.1007/3-540-57273-2_61;
Wikipedia, "Pathwidth" (section "Computing path-decompositions"), which records this result.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PathwidthChordalGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthBipartite

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-!
# PATHWIDTH OF BIPARTITE GRAPHS is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K`.
QUESTION: is the pathwidth of `G` at most `K`?

This is PATHWIDTH restricted to bipartite graphs (Mathlib's `SimpleGraph.IsBipartite`, a proper
2-coloring). Kloks, Bodlaender, Müller and Kratsch show that PATHWIDTH is NP-complete on
bipartite distance-hereditary graphs; bipartite graphs contain them, so PATHWIDTH stays
NP-complete on bipartite graphs (Wikipedia, "Pathwidth", records both statements with this
citation). Membership in NP is immediate (a path decomposition is a certificate).

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
the graph is bipartite, and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- PATHWIDTH OF BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def pathwidthBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphs.PathwidthChordalGraphsFeasible i)
  | none => false

/-- **PATHWIDTH OF BIPARTITE GRAPHS is NP-complete.**
Source: Kloks, Bodlaender, Müller and Kratsch (1993). -/
public theorem_wanted pathwidthBipartite_npComplete :
    pathwidthBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthBipartite
