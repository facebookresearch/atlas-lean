/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOSPITALS/RESIDENTS WITH COUPLES is NP-complete

Source:
E. Ronn, "NP-complete stable matching problems", Journal of Algorithms 11 (1990), 285-304,
doi:10.1016/0196-6774(90)90007-2;
E. J. McDermid and D. F. Manlove, "Keeping partners together: algorithmic results for the
hospitals/residents problem with couples", Journal of Combinatorial Optimization 19 (2010),
279-303, doi:10.1007/s10878-009-9257-2;
P. Biró, D. F. Manlove, and I. McBride, "The Hospitals / Residents problem with Couples:
complexity and integer programming models", Experimental Algorithms (SEA 2014), Lecture Notes in
Computer Science 8504, 10-21, doi:10.1007/978-3-319-07959-2_2; extended version
arXiv:1308.4534, Section 1.1.1 and Definition 1 (MM-stability), Section 1.2, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HospitalsResidentsWithCouplesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples

/-!
# HOSPITALS/RESIDENTS WITH COUPLES is NP-complete

INSTANCE (Biró, Manlove and McBride, Section 1.1.1): a set `H` of hospitals and a set `R` of
residents, partitioned into single residents and residents in couples; a set of couples
`(rᵢ, rⱼ)`, each resident in a couple belonging to exactly one couple. Each single resident has a
linear preference order over his acceptable hospitals; each couple `(rᵢ, rⱼ)` has a joint linear
preference order over a set `A ⊆ H × H` of acceptable pairs, `(h_p, h_q)` meaning `rᵢ` at `h_p`
and `rⱼ` at `h_q`; each hospital `hⱼ` has a capacity `cⱼ` and a linear preference order over the
residents who find `hⱼ` acceptable, as single residents or as members of couples.
A matching assigns residents to hospitals such that each single resident is unassigned or
assigned to an acceptable hospital, each couple is jointly unassigned or jointly assigned to an
acceptable pair, and no hospital exceeds its capacity.
QUESTION: is there an MM-stable matching (Definition 1, McDermid and Manlove's stability)?

Deciding whether a stable matching exists is NP-complete even with no single residents and all
capacities `1` (Ronn 1990, as recorded by Biró, Manlove and McBride, Section 1.2; their Theorem 1
proves it again for MM-stability with preference lists of length at most 2), and checking that a
matching is MM-stable takes polynomial time. With all capacities `1`, MM-stability is the
stability of Gusfield and Irving (Section 1.1.1).

Hospitals are `0, …, |H| - 1` in the order listed; residents are natural numbers; preference
lists are lists, most preferred first. A matching is a map from residents to `Option` hospitals
(`none`: unassigned). For a couple that is jointly unassigned, every acceptable pair is preferred
to its assignment.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HOSPITALS/RESIDENTS WITH COUPLES is NP-complete.** Source: Ronn (1990); McDermid and
Manlove (2010); Biró, Manlove and McBride (2014), Definition 1 and Theorem 1. -/
public theorem_wanted hospitalsResidentsWithCouples_npComplete :
    hospitalsResidentsWithCouplesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hospitalsResidentsWithCouplesDec

end MetaMathlibExt.Complexity.NPComplete.HospitalsResidentsWithCouples
