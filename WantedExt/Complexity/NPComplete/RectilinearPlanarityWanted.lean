/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR PLANARITY TESTING is NP-complete

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RectilinearPlanarityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity

/-!
# RECTILINEAR PLANARITY TESTING is NP-complete

"An undirected graph is rectilinear planar if it can be drawn in the plane such that every edge
is a horizontal or vertical segment and no two edges cross" (Garg and Tamassia).

INSTANCE: an undirected graph `G = (V, E)`.
QUESTION: is `G` rectilinear planar?

A drawing places each vertex at a point of `ℝ × ℝ`, injectively, and draws each edge as the
closed straight-line segment between its endpoints (MathlibExt's `SimpleGraph.Segment`). It is
rectilinear when every edge is horizontal or vertical (its endpoints share the first or the
second coordinate), and it has no crossing when two different edges meet only at common
endpoints and no vertex lies on an edge except at the edge's own endpoints. The edge-crossing
condition is the one of MathlibExt's straight-line planarity predicate `SimpleGraph.IsPlanar`,
so a rectilinear planar graph is planar. Every rectilinear planar graph
has maximum degree at most `4`: two edges leaving a vertex in the same of the four axis
directions overlap.

The graph is given by its vertex count `n` (vertices `0, …, n - 1`) and an edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECTILINEAR PLANARITY TESTING is NP-complete.** Source: Garg and Tamassia (2001). -/
public theorem_wanted rectilinearPlanarity_npComplete :
    rectilinearPlanarityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearPlanarityDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearPlanarity
