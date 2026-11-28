/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVotersDefs

namespace MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVoters

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers supporters)

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

/-- Feasibility ranges over the finitely many sublists of the unregistered votes. -/
private theorem feasible_iff (i : CondorcetConstructiveControlByAddingVotersInstance) :
    CondorcetConstructiveControlByAddingVotersFeasible i ↔ ∃ W' ∈ i.2.2.1.sublists,
      W'.length ≤ i.2.2.2.2 ∧ ∀ a d : Fin i.1, (a : ℕ) = i.2.2.2.1 → d ≠ a →
        (i.2.1 ++ W').length < 2 * (Finset.univ.filter fun j : Fin (i.2.1 ++ W').length =>
          (voteOrder (m := i.1) (i.2.1 ++ W')[j]).lt a d).card := by
  simp only [CondorcetConstructiveControlByAddingVotersFeasible, List.mem_sublists,
    IsCondorcetWinner, majority_iff]

/-- Registered votes `1 0 2` and `0 2 1` tie `0` against `1`; registering `0 1 2` makes `0` the
Condorcet winner. -/
private abbrev yes : CondorcetConstructiveControlByAddingVotersInstance :=
  (3, [[1, 0, 2], [0, 2, 1]], [[2, 1, 0], [0, 1, 2]], 0, 1)

/-- The same registered votes with unregistered votes `2 1 0` and `1 0 2`, neither of which
helps `0` against `1`. -/
private abbrev no : CondorcetConstructiveControlByAddingVotersInstance :=
  (3, [[1, 0, 2], [0, 2, 1]], [[2, 1, 0], [1, 0, 2]], 0, 1)

/-- The decision problem accepts `yes`, registering `[[0, 1, 2]]`. -/
example : condorcetConstructiveControlByAddingVotersDec (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed; decide
  have hf : CondorcetConstructiveControlByAddingVotersFeasible yes := by
    refine ⟨[[0, 1, 2]], by decide, by decide, ?_⟩
    unfold IsCondorcetWinner
    simp only [majority_iff]
    decide
  simp [condorcetConstructiveControlByAddingVotersDec, bitDecode_bitEncode, hw, hf]

/-- Without additions `0` is not the Condorcet winner of `yes`. -/
example : ¬ IsCondorcetWinner 3 [[1, 0, 2], [0, 2, 1]] 0 := by
  unfold IsCondorcetWinner
  simp only [majority_iff]
  decide

set_option synthInstance.maxSize 1024 in
/-- The decision problem rejects the well-formed instance `no`. -/
example : WellFormed no ∧ condorcetConstructiveControlByAddingVotersDec (bitEncode no) = false := by
  have hf : ¬ CondorcetConstructiveControlByAddingVotersFeasible no := by
    rw [feasible_iff]
    decide
  exact ⟨by unfold WellFormed; decide,
    by simp [condorcetConstructiveControlByAddingVotersDec, bitDecode_bitEncode, hf]⟩

/-- The registered vote `[0]` is not a ranking of the three candidates, so the instance is
malformed, although `0` already wins under the tie-breaking order on that list. -/
example :
    CondorcetConstructiveControlByAddingVotersFeasible
        ((3, [[0]], [[0, 1, 2]], 0, 1) : CondorcetConstructiveControlByAddingVotersInstance) ∧
      condorcetConstructiveControlByAddingVotersDec (bitEncode
        ((3, [[0]], [[0, 1, 2]], 0, 1) : CondorcetConstructiveControlByAddingVotersInstance)) =
          false := by
  have hw : ¬ WellFormed
      ((3, [[0]], [[0, 1, 2]], 0, 1) : CondorcetConstructiveControlByAddingVotersInstance) := by
    unfold WellFormed; decide
  refine ⟨⟨[], by simp, by decide, ?_⟩,
    by simp [condorcetConstructiveControlByAddingVotersDec, bitDecode_bitEncode, hw]⟩
  unfold IsCondorcetWinner
  simp only [majority_iff]
  decide

/-- A lone continuation bit is a truncated instance encoding. -/
example : condorcetConstructiveControlByAddingVotersDec [true] = false := by
  have h : bitDecode (α := CondorcetConstructiveControlByAddingVotersInstance) [true] = none := rfl
  simp [condorcetConstructiveControlByAddingVotersDec, h]

end MetaMathlibExt.Complexity.NPComplete.CondorcetConstructiveControlByAddingVoters
