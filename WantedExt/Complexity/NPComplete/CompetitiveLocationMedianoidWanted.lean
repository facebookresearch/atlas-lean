/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISCRETE (r|X_p)-MEDIANOID is NP-complete

Source:
S. L. Hakimi, "On locating new facilities in a competitive environment", European Journal of
Operational Research 12 (1983), 29-35, doi:10.1016/0377-2217(83)90180-7;
A. Lazar and A. Tamir, "Improved algorithms for some competitive location centroid problems
on paths, trees and graphs", Algorithmica 66 (2013), 615-640, doi:10.1007/s00453-012-9655-1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CompetitiveLocationMedianoidDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid

/-!
# DISCRETE (r|X_p)-MEDIANOID is NP-complete

The follower's problem of competitive location on a network, Hakimi's `(r|X_p)`-medianoid,
in its discrete form (new facilities at vertices). An instance is a graph with positive integer
edge lengths and nonnegative integer vertex weights (the customers' demand, located at the
vertices), a set `X_p` of vertices holding the competitor's existing facilities, an integer
`r` and a target `W`. A customer patronizes the follower only if a new facility is strictly
closer to it than every existing facility (shortest-path distance). The question is whether
`r` new facilities can be placed at vertices so that the total weight of the customers they
capture is at least `W`. All numbers are in binary encoding.

Lazar and Tamir (2013) record that Hakimi proved the absolute and the discrete
`(r|X)`-medianoid problems strongly NP-hard on general graphs, even when `X` is a single
vertex. NP membership is immediate (shortest-path distances are polynomial-time computable).

The `r` new facilities occupy `r` distinct vertices (a facility at a competitor's vertex
captures nothing there, as distance `0` is not strictly smaller). The graph need not be
connected: a vertex with no path to `X_p` is captured by a new facility it can reach, as its
distance to `X_p` is infinite; connected instances, which the source considers, are a special
case.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DISCRETE (r|X_p)-MEDIANOID is NP-complete.** Source: Hakimi (1983); Lazar and Tamir
(2013). -/
public theorem_wanted competitiveLocationMedianoid_npComplete :
    competitiveLocationMedianoidDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L competitiveLocationMedianoidDec

end MetaMathlibExt.Complexity.NPComplete.CompetitiveLocationMedianoid
