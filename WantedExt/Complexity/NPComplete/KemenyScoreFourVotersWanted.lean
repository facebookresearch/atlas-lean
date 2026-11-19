/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEMENY SCORE with four voters is NP-complete

Source:
C. Dwork, R. Kumar, M. Naor and D. Sivakumar, "Rank aggregation methods for the Web",
Proceedings of the 10th International World Wide Web Conference (WWW 2001), 613-622,
doi:10.1145/371920.372165, Appendix B, Theorem 11;
P. Madarasi, "The complexity of Kemeny aggregation with three rankings", arXiv:2607.28588
(2026), Lemma 30.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.KemenyScoreWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KemenyScoreFourVoters

/-!
# KEMENY SCORE with four voters is NP-complete

KEMENY SCORE (`WantedExt.Complexity.NPComplete.KemenyScoreWanted`) restricted to elections
with exactly four voters: given four rankings (total orders) of a set `C` of candidates and a
nonnegative integer `k`, is there a ranking of `C` whose total Kendall tau distance to the
four rankings is at most `k`? Dwork, Kumar, Naor and Sivakumar (2001), Theorem 11: computing a
Kemeny optimal permutation of `k` full lists is NP-hard for every even `k ≥ 4`, and the
corresponding decision problem is NP-complete. Madarasi (2026), Lemma 30, gives another proof
for four rankings, by a reduction from three rankings.

The instance and the question are those of KEMENY SCORE (`KemenyScore.KemenyScoreInstance`,
`KemenyScore.KemenyScoreFeasible`); this file adds only the restriction to four voters.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed KEMENY SCORE instance with exactly four
voters. -/
def WellFormed (i : KemenyScore.KemenyScoreInstance) : Prop :=
  KemenyScore.WellFormed i ∧ i.2.1.length = 4

open Classical in
/-- KEMENY SCORE with four voters as a decision problem over bitstrings. -/
noncomputable def kemenyScoreFourVotersDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KemenyScore.KemenyScoreInstance) x with
  | some i => decide (WellFormed i ∧ KemenyScore.KemenyScoreFeasible i)
  | none => false

/-- **KEMENY SCORE with four voters is NP-complete.** Source: Dwork, Kumar, Naor and
Sivakumar (2001), Theorem 11; Madarasi (2026), Lemma 30. -/
public theorem_wanted kemenyScoreFourVoters_npComplete :
    kemenyScoreFourVotersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kemenyScoreFourVotersDec

end MetaMathlibExt.Complexity.NPComplete.KemenyScoreFourVoters
