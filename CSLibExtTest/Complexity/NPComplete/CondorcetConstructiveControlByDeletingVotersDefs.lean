/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVotersDefs

namespace MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVoters

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers supporters)
open CondorcetConstructiveControlByAddingVoters (IsCondorcetWinner profile voteOrder)

private instance (m : ℕ) (v : List ℕ) (a b : Fin m) : Decidable ((voteOrder v).lt a b) :=
  inferInstanceAs (Decidable (v.idxOf (a : ℕ) < v.idxOf (b : ℕ) ∨
    (v.idxOf (a : ℕ) = v.idxOf (b : ℕ) ∧ (a : ℕ) < b)))

/-- Pairwise majority as a computable count of supporting votes. -/
private theorem majority_iff (m : ℕ) (E : List (List ℕ)) (a b : Fin m) :
    MajorityPrefers (profile m E) a b ↔ E.length <
      2 * (Finset.univ.filter fun j : Fin E.length => (voteOrder (m := m) E[j]).lt a b).card := by
  simp only [MajorityPrefers, supporters, profile, Fintype.card_fin]
  exact Iff.of_eq (congrArg (fun s : Finset (Fin E.length) => E.length < 2 * s.card)
    (Finset.filter_congr_decidable _ _ _))

/-- Feasibility ranges over the finitely many sublists of the votes. -/
private theorem feasible_iff (i : CondorcetConstructiveControlByDeletingVotersInstance) :
    CondorcetConstructiveControlByDeletingVotersFeasible i ↔ ∃ V' ∈ i.2.1.sublists,
      i.2.1.length ≤ V'.length + i.2.2.2 ∧ ∀ a d : Fin i.1, (a : ℕ) = i.2.2.1 → d ≠ a →
        V'.length < 2 * (Finset.univ.filter fun j : Fin V'.length =>
          (voteOrder (m := i.1) V'[j]).lt a d).card := by
  simp only [CondorcetConstructiveControlByDeletingVotersFeasible, List.mem_sublists,
    IsCondorcetWinner, majority_iff]

/-- Five votes; `0` beats `1` in only two of them. -/
private abbrev votes : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 2, 0], [2, 1, 0], [1, 0, 2]]

/-- Deleting up to two votes. -/
private abbrev yes : CondorcetConstructiveControlByDeletingVotersInstance := (3, votes, 0, 2)

/-- Deleting at most one vote leaves four, of which `0` beats `1` in at most two. -/
private abbrev no : CondorcetConstructiveControlByDeletingVotersInstance := (3, votes, 0, 1)

/-- The decision problem accepts `yes`, deleting `1 2 0` and `1 0 2`. -/
example : condorcetConstructiveControlByDeletingVotersDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : CondorcetConstructiveControlByDeletingVotersFeasible yes := by
    refine ⟨[[0, 1, 2], [0, 2, 1], [2, 1, 0]], by decide, by decide, ?_⟩
    unfold IsCondorcetWinner
    simp only [majority_iff]
    decide
  simp [condorcetConstructiveControlByDeletingVotersDec, bitDecode_bitEncode, hw, hf]

/-- Without deletions `0` is not the Condorcet winner. -/
example : ¬ IsCondorcetWinner 3 votes 0 := by
  unfold IsCondorcetWinner
  simp only [majority_iff]
  decide

set_option synthInstance.maxSize 1024 in
/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ condorcetConstructiveControlByDeletingVotersDec (bitEncode no) = false := by
  have hf : ¬ CondorcetConstructiveControlByDeletingVotersFeasible no := by
    rw [feasible_iff]
    decide
  exact ⟨by unfold WellFormed; decide,
    by simp [condorcetConstructiveControlByDeletingVotersDec, bitDecode_bitEncode, hf]⟩

/-- A zero bound is malformed, although `0` already wins the single vote `0 1 2`. -/
example :
    CondorcetConstructiveControlByDeletingVotersFeasible
        ((3, [[0, 1, 2]], 0, 0) : CondorcetConstructiveControlByDeletingVotersInstance) ∧
      condorcetConstructiveControlByDeletingVotersDec (bitEncode
        ((3, [[0, 1, 2]], 0, 0) : CondorcetConstructiveControlByDeletingVotersInstance)) =
          false := by
  have hw : ¬ WellFormed
      ((3, [[0, 1, 2]], 0, 0) : CondorcetConstructiveControlByDeletingVotersInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨[[0, 1, 2]], by simp, by decide, ?_⟩,
    by simp [condorcetConstructiveControlByDeletingVotersDec, bitDecode_bitEncode, hw]⟩
  unfold IsCondorcetWinner
  simp only [majority_iff]
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : condorcetConstructiveControlByDeletingVotersDec [true] = false := by
  have h : bitDecode (α := CondorcetConstructiveControlByDeletingVotersInstance) [true] = none :=
    rfl
  simp [condorcetConstructiveControlByDeletingVotersDec, h]

end MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByDeletingVoters
