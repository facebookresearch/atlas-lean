/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KEMENY SCORE: definitions

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "Voting schemes for which it can be
difficult to tell who won the election", Social Choice and Welfare 6 (1989), 157-165,
doi:10.1007/BF00303169;
C. Dwork, R. Kumar, M. Naor and D. Sivakumar, "Rank aggregation methods for the Web",
Proceedings of the 10th International World Wide Web Conference (WWW 2001), 613-622,
doi:10.1145/371920.372165, Appendix B, Theorem 11.
-/
module

public import CSLibExt.Algorithms.Lean.Online.ListUpdate
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KemenyScore

/-- An instance: the number `m` of candidates (candidates `0, …, m - 1`), the voters'
rankings, and the bound `k`. -/
abbrev KemenyScoreInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every voter's ranking is a total order of the candidates,
that is, a permutation of `List.range m`. -/
def WellFormed (i : KemenyScoreInstance) : Prop :=
  ∀ v ∈ i.2.1, v.Perm (List.range i.1)

/-- Some ranking `π` of the candidates (a permutation of `0, …, m - 1`) has total inversion count
`∑ ListUpdate.inv v π` at most `k` over the ballots `v`. The ballots are not required to be
rankings here; when they are, as well-formedness requires, `inv v π` is the Kendall tau
distance between `v` and `π`. -/
def KemenyScoreFeasible (i : KemenyScoreInstance) : Prop :=
  ∃ π : List ℕ, π.Perm (List.range i.1) ∧
    (i.2.1.map fun v => Cslib.Algorithms.Lean.Online.ListUpdate.inv v π).sum ≤ i.2.2

open Classical in
/-- KEMENY SCORE as a decision problem over bitstrings. -/
noncomputable def kemenyScoreDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KemenyScoreInstance) x with
  | some i => decide (WellFormed i ∧ KemenyScoreFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KemenyScore
