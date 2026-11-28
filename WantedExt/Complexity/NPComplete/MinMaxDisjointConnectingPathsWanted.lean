/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMUM DISJOINT CONNECTING PATHS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM MAXIMUM DISJOINT CONNECTING PATHS (decision version);
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "The complexity of finding two disjoint paths
with min-max objective function", Discrete Appl. Math. 26 (1990), 105-115,
doi:10.1016/0166-218X(90)90024-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinMaxDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxDisjointConnectingPaths

/-!
# MINIMUM MAXIMUM DISJOINT CONNECTING PATHS is NP-complete

INSTANCE: a graph `G = (V, E)`, a length function `l : E → ℕ`, a pair of vertices `s, t ∈ V`,
and a positive integer `K`.
QUESTION: are there two vertex-disjoint paths in `G` connecting `s` and `t` such that the
longer of the two (the larger of their total lengths) has length at most `K`?

This is the undirected, vertex-disjoint version of the problem of Li, McCormick and
Simchi-Levi (1990), who prove all four versions (vertex- or arc-disjoint, directed or
undirected) strongly NP-complete. The vertices are `0, ..., n - 1`; the graph is given by a
simple edge list whose entries `(u, v, l)` carry the length of the edge `{u, v}`, and `s ≠ t`.
Paths from `s` to `t` are Mathlib paths `G.Path s t`, and vertex-disjointness is
`IsInternallyVertexDisjointSTPaths` from `MathlibExt.Combinatorics.Graph.MengerVertex`: the two
paths share no vertex other than `s` and `t`. The two paths are required to be different, so a
single edge `{s, t}` cannot serve as both. The length of a path is the sum of the lengths of
its edges. Lengths are non-negative integers, as in Crescenzi and Kann, whose `N` denotes the
non-negative integers (their MAXIMUM INTEGER M-DIMENSIONAL KNAPSACK entry reads "nonnegative integer
`m × n`-matrix `A ∈ N^{m·n}`"), so an edge may have length `0`; the bound `K` is a positive integer.

Crescenzi and Kann write the paths as vertex sequences `s, u₁, …, u_m, t` and
`s, v₁, …, v_n, t` with `m, n ≥ 1`, which excludes the one-edge path along an edge `{s, t}`;
the statement here follows Li, McCormick and Simchi-Levi ("two disjoint paths from `s` to
`t`"), where that edge may be one of the two paths.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.SimpleGraph.MengerVertexWanted

/-- **MINIMUM MAXIMUM DISJOINT CONNECTING PATHS is NP-complete.** Source: Crescenzi and Kann,
MINIMUM MAXIMUM DISJOINT CONNECTING PATHS; Li, McCormick and Simchi-Levi (1990). -/
public theorem_wanted minMaxDisjointConnectingPaths_npComplete :
    minMaxDisjointConnectingPathsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minMaxDisjointConnectingPathsDec

end MetaMathlibExt.Complexity.NPComplete.MinMaxDisjointConnectingPaths
