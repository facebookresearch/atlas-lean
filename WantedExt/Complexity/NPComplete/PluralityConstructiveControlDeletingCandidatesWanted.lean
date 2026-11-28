/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "How hard is it to control an election?",
Mathematical and Computer Modelling 16 (1992), 27-40, doi:10.1016/0895-7177(92)90085-Y;
P. Faliszewski, E. Hemaspaandra, L. A. Hemaspaandra and J. Rothe, "Llull and Copeland voting
computationally resist bribery and constructive control", Journal of Artificial Intelligence
Research 35 (2009), 275-341, doi:10.1613/jair.2697 (arXiv:0809.4484), Section 2 (plurality,
the problem E-CCDC) and Table 1 (plurality resists constructive control by deleting candidates in
the unique-winner model, due to Bartholdi, Tovey and Trick).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidatesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidates

/-!
# PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete

INSTANCE: a set `C` of candidates, a collection `V` of voters represented via preference lists
over `C`, a distinguished candidate `p ∈ C`, and a nonnegative integer `k`. QUESTION: is it
possible, by deleting at most `k` candidates other than `p`, to make `p` the unique winner of the
resulting plurality election?

Plurality elects the candidates that are ranked first by the largest number of voters; after
deleting candidates, each voter's preference list is restricted to the remaining candidates, so
a voter's vote goes to the first remaining candidate of the list. `p` is the unique winner when
it receives strictly more votes than every other remaining candidate (Bartholdi, Tovey and
Trick's unique-winner model). Candidates are `0, …, m - 1`; each voter's list contains every
candidate exactly once, most preferred first; the voters form a list (a multiset). Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLURALITY CONSTRUCTIVE CONTROL BY DELETING CANDIDATES is NP-complete.** Source:
Bartholdi, Tovey and Trick (1992); Faliszewski, Hemaspaandra, Hemaspaandra and Rothe (2009),
Table 1. -/
public theorem_wanted pluralityConstructiveControlDeletingCandidates_npComplete :
    pluralityConstructiveControlDeletingCandidatesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L pluralityConstructiveControlDeletingCandidatesDec

end MetaMathlibExt.Complexity.NPComplete.PluralityConstructiveControlDeletingCandidates
