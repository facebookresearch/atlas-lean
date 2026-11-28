/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH OF CHORDAL GRAPHS is NP-complete

Source:
J. Gustedt, "On the pathwidth of chordal graphs", Discrete Applied Mathematics 45(3) (1993),
233-248, doi:10.1016/0166-218X(93)90012-D.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs

/-!
# PATHWIDTH OF CHORDAL GRAPHS is NP-complete

INSTANCE: a chordal graph `G = (V, E)` (every cycle of length at least `4` has a chord) and a
positive integer `K`.
QUESTION: does `G` have pathwidth at most `K`?

A path decomposition of `G` is a sequence of bags `X 0, …, X (r - 1)` of vertices such that every
vertex lies in some bag, both ends of every edge lie in a common bag, and the bags containing any
one vertex are consecutive (`IsPathDecomposition`). Its width is the largest bag size minus one,
and the pathwidth of `G` is the least width of a path decomposition; so the pathwidth is at most
`K` exactly when some path decomposition has all bags of size at most `K + 1`. (Equivalently, `G`
is a subgraph of an interval graph with clique number at most `K + 1`.)

Chordality is part of the instance class, so it is a conjunct of `WellFormed`: no cycle graph `Cₖ`
with `k ≥ 4` is an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and
`SimpleGraph.IsIndContained`; a cycle has a chord exactly when its vertices do not induce a cycle
graph). As in the source, `K` is positive.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PATHWIDTH OF CHORDAL GRAPHS is NP-complete.** Source: Gustedt (1993). -/
public theorem_wanted pathwidthChordalGraphs_npComplete :
    pathwidthChordalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pathwidthChordalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
