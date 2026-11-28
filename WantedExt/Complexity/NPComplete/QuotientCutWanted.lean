/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUOTIENT CUT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MINIMUM QUOTIENT
CUT;
J. K. Park and C. A. Phillips, "Finding minimum-quotient cuts in planar graphs", Proceedings
of the 25th Annual ACM Symposium on Theory of Computing (STOC 1993), 766-775,
doi:10.1145/167088.167284.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.QuotientCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuotientCut

/-!
# QUOTIENT CUT is NP-complete

INSTANCE: a graph `G = (V, E)`, a vertex-weight function `w : V → ℕ`, an edge-cost function
`c : E → ℕ`, and a positive integer `K`. QUESTION: is there a cut `C ⊆ V` whose quotient
`c(C) / min {w(C), w(V − C)}` is at most `K`, where `c(C)` is the sum of the costs of the
edges with exactly one endpoint in `C` and `w(V')` is the sum of the weights of the vertices
in `V'`?

This is the decision version of Crescenzi and Kann's MINIMUM QUOTIENT CUT (also called
minimum flux cut). Park and Phillips (abstract) state that "the minimum-quotient-cut problem is
strongly NP-hard for general graphs". An integer bound loses nothing: scaling the costs by
`q` and the weights by `p` turns a rational bound `p / q` into `1`. Membership in NP: `C` is a
certificate.

The quotient is defined only when `min {w(C), w(V − C)} > 0`, so a cut qualifies when this
minimum is positive and `c(C) ≤ K · min {w(C), w(V − C)}` (no division). The graph, weights and
costs are those of `BBalancedCut`, whose instance is this one plus a balance `b`: a quotient-cut
instance `(n, w, E, K)` is read as the `b`-balanced-cut instance `(n, w, E, 1/2, K)`, and
`WellFormed`, `BBalancedCut.weight` and `BBalancedCut.cutCost` are taken from there (the balance
is never used here). So the vertices are `0, ..., n - 1`, there is one weight per vertex, and
the edges `(u, v, c(e))` form a simple graph. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **QUOTIENT CUT is NP-complete.** Source: Crescenzi and Kann, MINIMUM QUOTIENT CUT; Park and
Phillips (1993). -/
public theorem_wanted quotientCut_npComplete :
    quotientCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quotientCutDec

end MetaMathlibExt.Complexity.NPComplete.QuotientCut
