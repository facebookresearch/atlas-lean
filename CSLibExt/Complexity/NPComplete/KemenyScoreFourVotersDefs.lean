/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEMENY SCORE with four voters: definitions

Source:
C. Dwork, R. Kumar, M. Naor and D. Sivakumar, "Rank aggregation methods for the Web",
Proceedings of the 10th International World Wide Web Conference (WWW 2001), 613-622,
doi:10.1145/371920.372165, Appendix B, Theorem 11;
P. Madarasi, "The complexity of Kemeny aggregation with three rankings", arXiv:2607.28588
(2026), Lemma 30.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.KemenyScoreDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KemenyScoreFourVoters

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

end MetaMathlibExt.Complexity.NPComplete.KemenyScoreFourVoters
