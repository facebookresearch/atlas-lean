/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHAPLEY-SHUBIK VOTING POWER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS8] SHAPLEY-SHUBIK VOTING POWER;
Y. Matsui and T. Matsui, "NP-completeness for calculating power indices of weighted majority
games", Theoretical Computer Science 263 (2001), 305-310, doi:10.1016/S0304-3975(00)00251-6
(Theorem 3, problem SS1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower

/-- An instance: the votes `[w(v₁), ..., w(vₙ)]` and the quota `q`. -/
abbrev ShapleyShubikVotingPowerInstance := List ℕ × ℕ

/-- Well-formedness of an instance: there is at least one voter, every voter has a positive
number of votes, and the quota is positive. -/
def WellFormed (i : ShapleyShubikVotingPowerInstance) : Prop :=
  0 < i.1.length ∧ (∀ w ∈ i.1, 0 < w) ∧ 0 < i.2

/-- Some ordering `π` of the voters has `v₁` (voter `0`) at a position `j` where the votes of
the first `j` voters total less than `q` and the votes of the first `j + 1` voters total at
least `q`. -/
def ShapleyShubikVotingPowerFeasible (i : ShapleyShubikVotingPowerInstance) : Prop :=
  ∃ π : List ℕ, π.Perm (List.range i.1.length) ∧ ∃ j, π[j]? = some 0 ∧
    ((π.take j).map (fun v => i.1.getD v 0)).sum < i.2 ∧
    i.2 ≤ ((π.take (j + 1)).map (fun v => i.1.getD v 0)).sum

open Classical in
/-- SHAPLEY-SHUBIK VOTING POWER as a decision problem over bitstrings. -/
noncomputable def shapleyShubikVotingPowerDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShapleyShubikVotingPowerInstance) x with
  | some i => decide (WellFormed i ∧ ShapleyShubikVotingPowerFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShapleyShubikVotingPower
