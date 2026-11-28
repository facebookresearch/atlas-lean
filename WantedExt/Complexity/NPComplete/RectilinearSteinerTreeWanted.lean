/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTILINEAR STEINER TREE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND13] GEOMETRIC STEINER TREE,
comment ("Remains so if the distance measure is replaced by the `L₁` "rectilinear" metric,
`|x₁ - x₂| + |y₁ - y₂|`");
M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM
Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RectilinearSteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerTree

/-!
# RECTILINEAR STEINER TREE is NP-complete

INSTANCE: a set `P ⊆ ℤ × ℤ` of points in the plane and a positive integer `K`.
QUESTION: is there a finite set `Q ⊆ ℤ × ℤ` such that there is a spanning tree of total
weight `K` or less for the vertex set `P ∪ Q`, where the weight of an edge
`{(x₁, y₁), (x₂, y₂)}` is the rectilinear (`L₁`) distance `|x₁ - x₂| + |y₁ - y₂|`?

Each integer coordinate is encoded as a pair of naturals `(positive part, negative part)`
representing their difference, and `P` is the set of the listed points (a repeated point
does not change it). A spanning tree for `P ∪ Q` is a graph `T` on the vertex type `P ∪ Q`
(a `Finset (ℤ × ℤ)`) that is a tree in Mathlib's sense (`SimpleGraph.IsTree`), so every point
of `P ∪ Q` is a vertex of `T`; its weight is the sum over its edges of the rectilinear
distance between their endpoints.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECTILINEAR STEINER TREE is NP-complete.** Source: Garey and Johnson (1979), [ND13],
comment; Garey and Johnson (1977). -/
public theorem_wanted rectilinearSteinerTree_npComplete :
    rectilinearSteinerTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectilinearSteinerTreeDec

end MetaMathlibExt.Complexity.NPComplete.RectilinearSteinerTree
