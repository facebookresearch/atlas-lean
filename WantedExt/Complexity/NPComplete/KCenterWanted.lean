/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CENTER (GENERALIZED, NONMETRIC) is NP-complete

Source:
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KCenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KCenter

/-!
# k-CENTER (GENERALIZED, NONMETRIC) is NP-complete

Generalized, nonmetric k-center: client-to-location costs (an arbitrary rectangular matrix of
natural numbers, one row per client, no metric assumed, clients and facilities distinct sets),
a bound `K` on the number of open locations, and a radius `B`. The question is whether at most
`K` locations can be opened so that every client is within cost `B` of an open location. The
metric p-center problem of Kariv-Hakimi is the special case of a metric cost matrix; hardness
follows from that subclass (e.g. the dominating-set reduction with costs 1 on edges, 2 on
nonedges, 0 on the diagonal, radius 1).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **k-CENTER (GENERALIZED, NONMETRIC) is NP-complete.** The decision problem of generalized
nonmetric k-center on bitstrings is NP-complete: it belongs to NP, and every decision problem in
NP has a polynomial-time many-one reduction to it.

Source: O. Kariv and S. L. Hakimi,
"An algorithmic approach to network location problems. I: The p-centers", SIAM Journal on
Applied Mathematics 37 (1979), 513-538. -/
public theorem_wanted kCenter_npComplete :
    kCenterDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kCenterDec

end MetaMathlibExt.Complexity.NPComplete.KCenter
