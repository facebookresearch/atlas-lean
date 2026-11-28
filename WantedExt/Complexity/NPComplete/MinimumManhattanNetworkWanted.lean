/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MANHATTAN NETWORK is NP-complete

Source:
F. Y. L. Chin, Z. Guo and H. Sun, "Minimum Manhattan network is NP-complete", Discrete and
Computational Geometry 45(4) (2011), 701-722, doi:10.1007/s00454-011-9342-z.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumManhattanNetworkDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumManhattanNetwork

/-!
# MINIMUM MANHATTAN NETWORK is NP-complete

INSTANCE: a finite set `T` of points in the plane with integer coordinates and a positive
integer `L`.
QUESTION: is there a set of axis-parallel segments of total length at most `L` containing an
`L₁`-shortest (monotone) path between every pair of points of `T`?

Chin, Guo and Sun: "a Manhattan network on T is a graph G with the property that for each pair
of points in T, G contains a rectilinear path between them of length equal to their distance in
the L₁-metric. The minimum Manhattan network problem is to find a Manhattan network of minimum
length, i.e., minimizing the total length of the line segments in the network"; they prove the
decision version strongly NP-complete.

The network is a finite list of closed axis-parallel segments with real endpoints (Mathlib's
`segment ℝ`), and its length is the sum of the segment lengths. A rectilinear path is a list of
points `w₀, …, w_k` in which consecutive points share a coordinate and the segment between them
lies in the union of the network's segments; its length is the sum of the `L₁` distances
`|x - x'| + |y - y'|` of consecutive points. A path from `p` to `q` has length at least the
`L₁` distance from `p` to `q`, and the question asks for one of exactly that length.
Overlapping segments are counted with multiplicity, which does not change the answer: the union
of finitely many axis-parallel segments is the union of finitely many non-overlapping ones whose
total length is the length of the union. A path may turn wherever segments meet, as in the
graph obtained by subdividing the segments at their intersection points.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Each integer coordinate is a pair
`(p, q)` of naturals standing for `p - q`, and `T` is the set of the listed points (a repeated
point does not change it).

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM MANHATTAN NETWORK is NP-complete.** Source: Chin, Guo and Sun (2011). -/
public theorem_wanted minimumManhattanNetwork_npComplete :
    minimumManhattanNetworkDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumManhattanNetworkDec

end MetaMathlibExt.Complexity.NPComplete.MinimumManhattanNetwork
