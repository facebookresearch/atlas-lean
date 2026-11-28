/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEOMETRIC STEINER TREE in the L∞ metric is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC STEINER TREE, p. 209
(comment: "Remains so if the distance measure is replaced by the L₁ "rectilinear" metric,
|x₁ − x₂| + |y₁ − y₂|, [Garey and Johnson, 1977a] or the L∞ metric, max {|x₁ − x₂|, |y₁ − y₂|},
which is equivalent to L₁ under a 45° rotation");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LInfinitySteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree

open RectilinearSteinerTree (RectilinearSteinerTreeInstance points)

/-!
# GEOMETRIC STEINER TREE in the L∞ metric is NP-complete

INSTANCE: a set `P ⊆ ℤ × ℤ` of points in the plane and a positive integer `K`.
QUESTION: is there a finite set `Q ⊆ ℤ × ℤ` such that there is a spanning tree of total
weight `K` or less for the vertex set `P ∪ Q`, where the weight of an edge
`{(x₁, y₁), (x₂, y₂)}` is the `L∞` distance `max {|x₁ - x₂|, |y₁ - y₂|}`?

This is the `L∞` variant in Garey and Johnson's comment to [ND13]. The instance encoding, the
point set `points` and `WellFormed` (`0 < K`) are those of the `L₁` variant,
`WantedExt.Complexity.NPComplete.RectilinearSteinerTreeWanted`, reused unchanged; the edge weight
is the `L∞` distance (`chebyshev`) in place of the rectilinear one, and the spanning tree is, as
there, a graph on the vertex type `P ∪ Q` (a `Finset (ℤ × ℤ)`) that is a Mathlib
`SimpleGraph.IsTree`, weighted by the sum over its edges.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GEOMETRIC STEINER TREE in the `L∞` metric is NP-complete.** Source: Garey and Johnson
(1979), [ND13], comment; Garey and Johnson (1977). -/
public theorem_wanted lInfinitySteinerTree_npComplete :
    lInfinitySteinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L lInfinitySteinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.LInfinitySteinerTree
