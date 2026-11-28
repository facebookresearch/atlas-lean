/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete

Source:
N. Megiddo, E. Zemel, and S. L. Hakimi, "The maximum coverage location problem", SIAM Journal
on Algebraic and Discrete Methods 4 (1983), 253-261, doi:10.1137/0604028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumCoverageLocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation

/-!
# MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete

INSTANCE: a graph `G = (V, E)` with a length `d(e) ∈ ℤ₀⁺` for each edge `e ∈ E`, a customer at
each vertex `v` with a gain `w(v) ∈ ℤ₀⁺` and a positive rational threshold radius `r(v)`, a
number `p` of new facilities, and a target `W`. QUESTION: can `p` facilities be located at
points of `G` (a point is a vertex or a point on an edge, the edge regarded as a line segment of
length `d(e)`) so that the customers covered, those `v` at distance less than `r(v)` from some
facility, have total gain at least `W`?

This is the maximum coverage location problem of Megiddo, Zemel, and Hakimi (1983) in decision
form: the distance between points is the length of a shortest route along the edges, a customer
`v` switches to a new facility "located at a distance less than `r_v`" (their abstract; §2
defines the `r_v`-neighborhood of `v` as the points at distance less than `r_v`), facilities may
be located anywhere on `G`, including interior points of edges, and the objective is the total
gain of the covered customers. They note that the problem is NP-hard on general graphs, by
expressing MINIMUM DOMINATING SET with unit lengths, unit gains, `r_v = 1.5` and `W = |V|`, and
solve it in polynomial time on trees. Binary encoding of all numbers.

A point is a triple `(a, b, t)`: the vertex `a` when `a = b` and `t = 0`, or, when `{a, b} ∈ E`,
the point of that edge at distance `t ∈ [0, d({a, b})]` from `a` (real `t`, as on a segment). A
shortest route from a vertex `v` to the point `(a, b, t)` enters it from `a` or from `b`, so its
length is `min (δ(v, a) + t, δ(v, b) + d({a, b}) - t)`, where `δ(v, a)` is the least total length
of a `SimpleGraph.Walk` from `v` to `a`. `DistLT i v x r` states that this distance is less than
`r`, existentially over walks. At most `p` facilities are located: more facilities never cover
fewer customers, and a point written in two ways is counted twice, which is harmless. Megiddo
et al. (§2) show that the facilities can be restricted to a finite candidate set of `O(|E| |V|)`
points determined by the distances and radii, so a certificate of polynomial size exists.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The radius `r(v)` is a pair
`(a, b)` of naturals with `a > 0` and `b > 0`, standing for `a / b`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM COVERAGE LOCATION ON A NETWORK is NP-complete.** Source: Megiddo, Zemel, and
Hakimi (1983). -/
public theorem_wanted maximumCoverageLocation_npComplete :
    maximumCoverageLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCoverageLocationDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCoverageLocation
