/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BISECTION on unit disk graphs is NP-complete

Source:
J. Díaz and G. B. Mertzios, "Minimum bisection is NP-hard on unit disk graphs", Information and
Computation 256 (2017), 83-92, doi:10.1016/j.ic.2017.04.010 (conference version MFCS 2014,
LNCS 8635, 251-262, doi:10.1007/978-3-662-44465-8_22; preprint arXiv:1404.0117).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinBisectionUnitDiskGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinBisectionUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
  (MaxCutUnitDiskGraphsInstance toMaxCut)
open MetaMathlibExt.Complexity.NPComplete.MinBisection (MinBisectionFeasible)

/-!
# MINIMUM BISECTION on unit disk graphs is NP-complete

INSTANCE: a unit disk graph `G = (V, E)` given with a unit disk representation, and a positive
integer `K`. QUESTION: is there a bisection of `G`, a partition of `V` into two sets of sizes
`⌊|V| / 2⌋` and `⌈|V| / 2⌉`, with at most `K` edges between the two sets?

Díaz and Mertzios prove MIN-BISECTION NP-hard on unit disk graphs. Recognizing unit disk graphs
is NP-hard, so, as in `WantedExt.Complexity.NPComplete.MaxCutUnitDiskGraphsWanted`, the
instance carries the representation; the instance and its well-formedness are that module's,
reused unchanged: distinct disk centers with rational coordinates (`RatCode`), a simple edge list
on the vertices `0, …, |P| - 1` equal to the unit disk graph of the centers, and `K` positive
(as there; the case `K = 0` is not needed for hardness). The question is MINIMUM BISECTION's
(`WantedExt.Complexity.NPComplete.MinBisectionWanted`) on `(|P|, E, K)`: a set `S` of
`⌊|P| / 2⌋` vertices such that no `K + 1` edges cross between `S` and its complement. That
module's well-formedness requires `|V|` even; Díaz and Mertzios define a bisection for every
`|V|` (part sizes `⌊|V| / 2⌋` and `⌈|V| / 2⌉`), so only its question is reused. Membership in
NP: the set `S` is the certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM BISECTION on unit disk graphs is NP-complete.** Source: Díaz and Mertzios (2017). -/
public theorem_wanted minBisectionUnitDiskGraphs_npComplete :
    minBisectionUnitDiskGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minBisectionUnitDiskGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MinBisectionUnitDiskGraphs
