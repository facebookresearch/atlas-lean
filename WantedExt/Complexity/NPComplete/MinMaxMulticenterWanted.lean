/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-MAX MULTICENTER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinMaxMulticenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter

/-!
# MIN-MAX MULTICENTER is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(v) ∈ ℤ₀⁺` for each `v ∈ V`, a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a positive integer `K ≤ |V|`, and a positive rational `B`.
QUESTION: is there a set `P` of `K` "points on `G`" (a point on `G` is either a vertex in `V` or
a point on an edge `e ∈ E`, with `e` regarded as a line segment of length `l(e)`) such that, if
`d(v)` is the length of the shortest path from `v` to the closest point in `P`, then
`max {d(v) · w(v) : v ∈ V} ≤ B`?

This is the absolute (points on edges allowed), vertex-weighted p-center problem of Kariv and
Hakimi, in Garey and Johnson's decision form. Binary encoding of all numbers.

A point is a triple `(a, b, t)`: the vertex `a` when `a = b` and `t = 0`, or, when `{a, b} ∈ E`,
the point of that edge at distance `t ∈ [0, l({a, b})]` from `a` (real `t`, as on a segment). A
shortest path from a vertex `v` to the point `(a, b, t)` enters it from `a` or from `b`, so
`d(v, (a, b, t)) = min (d(v, a) + t, d(v, b) + l({a, b}) - t)`, where `d(v, a)` is the least
total length of a `SimpleGraph.Walk` from `v` to `a`. `DistLE i v p r` states
`d(v, p) ≤ r` this way, existentially over walks. The question then reads: every vertex `v` has
a point `p ∈ P` and a bound `r ≥ d(v, p)` with `w(v) · r ≤ B`.

Two conventions are fixed and disclosed. `P` has at most `K` points: more points never increase
any `d(v)`, and `K ≤ |V|` vertices are available, so "at most `K`" and "exactly `K`" agree (and a
point written in two ways is counted twice, which is harmless). `d(v)` is the length of a
shortest path from `v` to `P`, so it is defined only when such a path exists: every vertex must
reach a point of `P` (on a disconnected graph, `P` needs a point in every component), whatever
its weight.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The rational `B` is a pair
`(p, q)` of naturals with `q > 0`, standing for `p / q`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MIN-MAX MULTICENTER is NP-complete.** Source: Garey and Johnson (1979), [ND50]; Kariv and
Hakimi (1979). -/
public theorem_wanted minMaxMulticenter_npComplete :
    minMaxMulticenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minMaxMulticenterDec

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter
