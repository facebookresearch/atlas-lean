/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B-BALANCED CUT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MINIMUM B-BALANCED CUT;
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1 (1976), 237-267, doi:10.1016/0304-3975(76)90059-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO BOUNDED SETS, comment;
T. N. Bui and C. Jones, "Finding good approximate vertex and edge partitions is NP-hard",
Information Processing Letters 42 (1992), 153-159, doi:10.1016/0020-0190(92)90140-Q.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BBalancedCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BBalancedCut

/-!
# B-BALANCED CUT is NP-complete

INSTANCE: a graph `G = (V, E)`, a vertex-weight function `w : V → ℕ`, an edge-cost function
`c : E → ℕ`, a rational `b` with `0 < b ≤ 1/2`, and a positive integer `K`.
QUESTION: is there a cut `C ⊆ V` with `min {w(C), w(V − C)} ≥ b · w(V)`, where `w(V')` is the
sum of the weights of the vertices in `V'`, whose weight `∑_{e ∈ δ(C)} c(e)` is at most `K`,
where `δ(C)` is the set of edges with one endpoint in `C` and one in `V − C`?

This is the decision version of Crescenzi and Kann's MINIMUM B-BALANCED CUT (also called
minimum `b`-edge separator). Its instances with unit vertex weights, unit edge costs and
`b = 1/2` ask for a bisection, a cut into two halves of `|V|/2` vertices, crossing at most `K`
edges; this is MINIMUM BISECTION, NP-complete by Garey, Johnson and Stockmeyer (Garey and
Johnson [ND17], comment: "Remains NP-complete for B = |V|/2 and w(e) = 1 for all e ∈ E").
Bui and Jones (abstract) record that "it is NP-hard to find optimal α-edge separators for
general graphs".

Encoding: the vertices are `0, …, n - 1`; the vertex weights are listed in vertex order; the
edges are listed as `(u, v, c(e))` with `u ≠ v`, endpoints below `n` and at most one edge per
unordered pair (a simple graph); `b = p / q` is given by natural numbers with `0 < p` and
`2 * p ≤ q` (so `0 < b ≤ 1/2`), and the balance condition is
`p · w(V) ≤ q · min {w(C), w(V − C)}`. A cut is a finite set `C` of vertices. Binary encoding of
all numbers.
The instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **B-BALANCED CUT is NP-complete.** Source: Crescenzi and Kann, MINIMUM B-BALANCED CUT; Garey,
Johnson and Stockmeyer (1976); Bui and Jones (1992). -/
public theorem_wanted bBalancedCut_npComplete :
    bBalancedCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bBalancedCutDec

end MetaMathlibExt.Complexity.NPComplete.BBalancedCut
