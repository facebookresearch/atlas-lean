/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-SUM MULTICENTER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND51] MIN-SUM MULTICENTER;
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. II: The
p-medians", SIAM Journal on Applied Mathematics 37 (1979), 539-560, doi:10.1137/0137041.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinSumMulticenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

/-!
# MIN-SUM MULTICENTER is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight `w(v) ∈ ℤ₀⁺` for each `v ∈ V`, a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a positive integer `K ≤ |V|`, and a positive rational `B`.
QUESTION: is there a set `P` of `K` "points on `G`" (a point on `G` is either a vertex in `V` or
a point on an edge `e ∈ E`, with `e` regarded as a line segment of length `l(e)`) such that, if
`d(v)` is the length of the shortest path from `v` to the closest point in `P`, then
`∑_{v ∈ V} d(v) · w(v) ≤ B`?

This is the vertex-weighted p-median problem of Kariv and Hakimi, in Garey and Johnson's
decision form, with points on edges allowed as in the source (an optimal `P` can be taken
among the vertices, a classical result of Hakimi, but the statement does not rely on it).
Binary encoding of all numbers.

A point is a triple `(a, b, t)`: the vertex `a` when `a = b` and `t = 0`, or, when `{a, b} ∈ E`,
the point of that edge at distance `t ∈ [0, l({a, b})]` from `a` (real `t`, as on a segment). A
shortest path from a vertex `v` to the point `(a, b, t)` enters it from `a` or from `b`, so
`d(v, (a, b, t)) = min (d(v, a) + t, d(v, b) + l({a, b}) - t)`, where `d(v, a)` is the least
total length of a `SimpleGraph.Walk` from `v` to `a`. `DistLE i v p r` states
`d(v, p) ≤ r` this way, existentially over walks. The question then reads: there are bounds
`r(v)`, each `r(v) ≥ d(v, p)` for some `p ∈ P`, with `∑_{v ∈ V} w(v) · r(v) ≤ B`; since
`w(v) ≥ 0`, this holds iff `∑_{v ∈ V} w(v) · d(v) ≤ B` (take `r(v) = d(v)`).

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

/-- **MIN-SUM MULTICENTER is NP-complete.** Source: Garey and Johnson (1979), [ND51]; Kariv and
Hakimi (1979). -/
public theorem_wanted minSumMulticenter_npComplete :
    minSumMulticenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minSumMulticenterDec

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter
