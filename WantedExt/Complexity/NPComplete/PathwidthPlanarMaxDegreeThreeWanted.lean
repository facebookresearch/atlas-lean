/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF PLANAR GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

Source:
B. Monien and I. H. Sudborough, "Min cut is NP-complete for edge weighted trees", Theoretical
Computer Science 58 (1988), 209-229, doi:10.1016/0304-3975(88)90028-X (Vertex Separation for
planar graphs of maximum vertex degree 3);
N. G. Kinnersley, "The vertex separation number of a graph equals its path-width", Information
Processing Letters 42 (1992), 345-350, doi:10.1016/0020-0190(92)90234-M.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathwidthPlanarMaxDegreeThreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance Graph)

/-!
# PATHWIDTH OF PLANAR GRAPHS OF MAXIMUM DEGREE 3 is NP-complete

INSTANCE: a planar graph `G = (V, E)` with every vertex degree at most `3`, and a positive
integer `K`.
QUESTION: is the pathwidth of `G` at most `K`?

This is PATHWIDTH restricted to planar graphs of maximum degree `3`. The instance, the graph and
the question are those of the merged `PathwidthChordalGraphsWanted`, reused unchanged: vertex
count, edge list on `Fin n` and bound `K` (`PathwidthChordalGraphsInstance`,
`PathwidthChordalGraphs.Graph`), and the question
`PathwidthChordalGraphs.PathwidthChordalGraphsFeasible`: some path decomposition
(`PathwidthChordalGraphs.IsPathDecomposition`) has every bag of size at most `K + 1`. That
question does not mention chordality. Well-formedness is the parent's simple-edge-list condition
and `0 < K` (as in `PathwidthWanted`), with the class restriction: planarity as the repository's
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, which by Fáry's theorem exists
exactly for planar graphs) and the degree bound as Mathlib's `SimpleGraph.degree`.

Monien and Sudborough prove that VERTEX SEPARATION is NP-complete for planar graphs of maximum
vertex degree `3`; Kinnersley proves that the vertex separation number of a graph equals its
pathwidth. Membership in NP: a path decomposition is a certificate, and planarity and degrees are
checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATHWIDTH OF PLANAR GRAPHS OF MAXIMUM DEGREE 3 is NP-complete.** Source: Monien and
Sudborough (1988); Kinnersley (1992). -/
public theorem_wanted pathwidthPlanarMaxDegreeThree_npComplete :
    pathwidthPlanarMaxDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthPlanarMaxDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthPlanarMaxDegreeThree
