/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERSECTION GRAPH FOR SEGMENTS ON A GRID is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND46] INTERSECTION GRAPH FOR SEGMENTS ON A
GRID, p. 219, crediting F. Gavril, "Some NP-complete problems on graphs", Proceedings of the
11th Conference on Information Sciences and Systems, Johns Hopkins University, Baltimore (1977),
91-95 (transformation from 3-PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGridDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid

/-!
# INTERSECTION GRAPH FOR SEGMENTS ON A GRID is NP-complete

INSTANCE: a graph `G = (V, E)` and positive integers `M`, `N`.
QUESTION: is `G` the intersection graph for a set of line segments on an `M × N` grid, i.e. is
there a one-to-one function `f` that maps each `v ∈ V` to a line segment
`f(v) = [(x, y), (z, w)]`, where `1 ≤ x ≤ z ≤ M`, `1 ≤ y ≤ w ≤ N`, and either `x = z` or
`y = w`, such that `{u, v} ∈ E` if and only if the line segments `f(u)` and `f(v)` intersect?

A segment `[(x, y), (z, w)]` is MathlibExt's closed straight-line segment
`SimpleGraph.Segment (x, y) (z, w)` in `ℝ × ℝ` (a single point when `x = z` and `y = w`), and
two segments intersect when they share a point. The "if and only if" is required for distinct
vertices `u ≠ v` (a segment always meets itself, while the graph has no loops).

Membership in NP with the vertex count `n` in binary: only the vertices incident to an edge
(at most `2|E|`) need segments in a certificate. An isolated vertex can always take a single
grid point covered by no other segment (a point meets only segments through it), and in any
representation each isolated vertex's segment has an endpoint on no other segment, distinct for
distinct isolated vertices. So the instance is a yes-instance iff some placement of the
non-isolated vertices leaves at least as many uncovered points of the `M × N` grid as there are
isolated vertices, and that count is computed in polynomial time from the at most `2|E|` axis-
parallel segments (merge overlapping segments per line, then subtract crossings).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTERSECTION GRAPH FOR SEGMENTS ON A GRID is NP-complete.** Source: Garey and Johnson
(1979), [ND46]; Gavril (1977). -/
public theorem_wanted intersectionGraphForSegmentsOnAGrid_npComplete :
    intersectionGraphForSegmentsOnAGridDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intersectionGraphForSegmentsOnAGridDec

end MetaMathlibExt.Complexity.NPComplete.IntersectionGraphForSegmentsOnAGrid
