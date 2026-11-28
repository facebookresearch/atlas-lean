/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEMENY SCORE is NP-complete

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "Voting schemes for which it can be
difficult to tell who won the election", Social Choice and Welfare 6 (1989), 157-165,
doi:10.1007/BF00303169;
C. Dwork, R. Kumar, M. Naor and D. Sivakumar, "Rank aggregation methods for the Web",
Proceedings of the 10th International World Wide Web Conference (WWW 2001), 613-622,
doi:10.1145/371920.372165, Appendix B, Theorem 11.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.KemenyScoreDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KemenyScore

/-!
# KEMENY SCORE is NP-complete

An election has a set `C` of candidates and a collection of voters, each with a ranking (a
total order) of `C`; several voters may cast the same ranking. The Kemeny objective of a
ranking `π` of `C` is the sum, over the voters, of the Kendall tau distance from the voter's
ranking to `π`, the number of candidate pairs the two rankings order differently. KEMENY
SCORE: given an election and a nonnegative integer `k`, is there a ranking of `C` whose
Kemeny objective is at most `k`? Bartholdi, Tovey and Trick (1989) proved it NP-complete;
Dwork, Kumar, Naor and Sivakumar (2001), Theorem 11, proved the decision problem
NP-complete already for every fixed even number `≥ 4` of voters.

Candidates are `0, …, m - 1`. A ranking is a list that is a permutation of
`List.range m`, listing the candidates from most to least preferred. The Kendall tau distance
is `Cslib.Algorithms.Lean.Online.ListUpdate.inv`, the number of pairs `(a, b)` with `a` before
`b` in the first list and `b` before `a` in the second.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **KEMENY SCORE is NP-complete.** Source: Bartholdi, Tovey and Trick (1989); Dwork, Kumar,
Naor and Sivakumar (2001), Theorem 11. -/
public theorem_wanted kemenyScore_npComplete :
    kemenyScoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kemenyScoreDec

end MetaMathlibExt.Complexity.NPComplete.KemenyScore
