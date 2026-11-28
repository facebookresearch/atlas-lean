/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TERRAIN GUARDING is NP-complete

Source:
J. King and E. Krohn, "Terrain guarding is NP-hard", SIAM Journal on Computing 40(5) (2011),
1316-1339, doi:10.1137/100791506 (arXiv:0907.1280, Section 2: the reduction from planar
3-SAT is for the discrete terrain guarding problem, "where both the set of guards and the set
of points to be guarded are a finite subset of the terrain").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TerrainGuardingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TerrainGuarding

/-!
# TERRAIN GUARDING is NP-complete

INSTANCE: a 1.5-dimensional terrain `T`, that is, an `x`-monotone polygonal chain given by its
vertices `v₁, …, vₙ` with `vᵢ = (xᵢ, yᵢ)` and `xᵢ < xᵢ₊₁`, with an edge joining each pair
`vᵢ, vᵢ₊₁`; a finite set `G` of candidate guard points on the terrain; a finite set `N` of
points on the terrain; and an integer `K`.
QUESTION: is there a set of at most `K` guards from `G` such that every point of `N` is seen
by one of them? A point `p` on the terrain sees a point `q` on the terrain if the line segment
`pq` is never strictly below the terrain.

This is the discrete version of the problem, the one the source's reduction targets. Points
are elements of `ℝ × ℝ` with rational coordinates; the terrain is the union of its edges, each
the Mathlib `segment` between consecutive vertices. A segment point `z` is strictly below the
terrain when a terrain point `t` with the same `x`-coordinate has `t.2 > z.2`. A rational
number is given as the positive and negative parts of its numerator and its denominator, which
must be positive; coordinates and `K` use the canonical binary encoding. The terrain has at
least two vertices, so it has at least one edge.

Membership in NP: a certificate is the chosen guard set; since the terrain is piecewise linear,
whether `p` sees `q` is decided by comparing the segment `pq` with the terrain vertices between
them, in rational arithmetic.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TERRAIN GUARDING is NP-complete.** Source: King and Krohn (2011). -/
public theorem_wanted terrainGuarding_npComplete :
    terrainGuardingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L terrainGuardingDec

end MetaMathlibExt.Complexity.NPComplete.TerrainGuarding
