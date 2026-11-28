/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL DOMINATING SET is NP-complete

Source:
E. J. Cockayne, R. M. Dawes, and S. T. Hedetniemi, "Total domination in graphs", Networks 10
(1980), 211-219; R. Laskar, J. Pfaff, S. M. Hedetniemi, and S. T. Hedetniemi, "On the
algorithmic complexity of total domination", SIAM Journal on Algebraic and Discrete Methods 5
(1984), 420-425.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TotalDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet

/-!
# TOTAL DOMINATING SET is NP-complete

An undirected graph and a bound `K`. The question is whether some set `S` of at most `K`
vertices totally dominates the graph: every vertex, including those in `S`, has a neighbor in
`S` (open-neighborhood domination). An isolated vertex makes the instance a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TOTAL DOMINATING SET is NP-complete.** The decision problem TOTAL DOMINATING SET belongs to
NP, and every decision problem in NP reduces to TOTAL DOMINATING SET by a polynomial-time
many-one reduction.

Source: E. J. Cockayne, R. M. Dawes, and S. T.
Hedetniemi, "Total domination in graphs", Networks 10 (1980), 211-219; R. Laskar, J.
Pfaff, S. M. Hedetniemi, and S. T. Hedetniemi, "On the algorithmic complexity of total
domination", SIAM Journal on Algebraic and Discrete Methods 5 (1984), 420-425. -/
public theorem_wanted totalDominatingSet_npComplete :
    totalDominatingSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L totalDominatingSetDec

end MetaMathlibExt.Complexity.NPComplete.TotalDominatingSet
