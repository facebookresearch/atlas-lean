/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPWARD PLANARITY TESTING is NP-complete

Source:
A. Garg and R. Tamassia, "On the computational complexity of upward and rectilinear planarity
testing", SIAM Journal on Computing 31 (2001), 601-625, doi:10.1137/S0097539794277123;
G. Di Battista and R. Tamassia, "Algorithms for plane representations of acyclic digraphs",
Theoretical Computer Science 61 (1988), 175-198, doi:10.1016/0304-3975(88)90123-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UpwardPlanarityTestingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting

/-!
# UPWARD PLANARITY TESTING is NP-complete

Given a directed acyclic graph `D`, is `D` upward planar, that is, does it have a planar drawing
in which every arc is a curve that is monotonically increasing in the vertical direction?
Garg and Tamassia (2001): "A directed graph is upward planar if it can be drawn in the plane
such that every edge is a monotonically increasing curve in the vertical direction and no two
edges cross", and they show that testing upward planarity is NP-complete.

The drawing is stated in straight-line form: vertices are distinct points of `ℝ × ℝ`, every arc
`u → v` is the segment from `u` to `v` with `u` strictly below `v`, the segments of two arcs
with different endpoint sets meet only in common endpoints (the crossing-free condition of the
shared MathlibExt predicate `SimpleGraph.IsPlanar`, built on its `SimpleGraph.Segment`), and no
vertex lies on the segment of an arc unless it is an endpoint of that arc. By Di
Battista and Tamassia (1988), every upward planar digraph has a planar straight-line upward
drawing, so this is upward planarity.

Acyclicity is part of the instance class (no vertex reaches itself by a nonempty directed path);
it excludes loops and antiparallel arcs. It does not change the language: a digraph with a
directed cycle has no upward drawing. Vertices are `Fin n`; isolated vertices never affect upward
planarity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UPWARD PLANARITY TESTING is NP-complete.** Source: Garg and Tamassia (2001); straight-line
form by Di Battista and Tamassia (1988). -/
public theorem_wanted upwardPlanarityTesting_npComplete :
    upwardPlanarityTestingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L upwardPlanarityTestingDec

end MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting
