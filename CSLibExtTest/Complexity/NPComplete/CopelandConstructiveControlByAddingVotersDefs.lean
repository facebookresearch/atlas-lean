/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVotersDefs

namespace MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers supporters)
open CondorcetConstructiveControlByAddingVoters
  (CondorcetConstructiveControlByAddingVotersInstance profile voteOrder)

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
private theorem feasible_iff (α : ℚ) (i : CondorcetConstructiveControlByAddingVotersInstance) :
    CopelandConstructiveControlByAddingVotersFeasible α i ↔ ∃ Q ∈ i.2.2.1.sublists,
      Q.length ≤ i.2.2.2.2 ∧ IsUniqueCopelandWinner α i.1 (i.2.1 ++ Q) i.2.2.2.1 := by
  simp only [CopelandConstructiveControlByAddingVotersFeasible, List.mem_sublists]

/-- Registered votes `1 0 2` and `0 2 1`: `0` ties `1`, beats `2`, and `1` ties `2`, so the
scores are `1 + α`, `2α` and `α`; `0` is the unique winner exactly when `α < 1`. -/
private abbrev registered : List (List ℕ) := [[1, 0, 2], [0, 2, 1]]

/-- Registering `0 1 2` makes `0` beat both other candidates. -/
private abbrev yes : CondorcetConstructiveControlByAddingVotersInstance :=
  (3, registered, [[2, 1, 0], [0, 1, 2]], 0, 1)

/-- Each unregistered vote `2 1 0` or `1 0 2` makes `1` beat `0`. -/
private abbrev no : CondorcetConstructiveControlByAddingVotersInstance :=
  (3, registered, [[2, 1, 0], [1, 0, 2]], 0, 1)

private theorem yes_wellFormed : WellFormed yes := by unfold WellFormed; decide

private theorem no_wellFormed : WellFormed no := by unfold WellFormed; decide

/-- After registering `0 1 2`, `0` is the unique Copeland^α winner for every `α`. -/
private theorem winner_after (α : ℚ) : IsUniqueCopelandWinner α 3 (registered ++ [[0, 1, 2]]) 0 := by
  unfold IsUniqueCopelandWinner copelandScore
  simp only [majority_iff]
  have h0 : ∀ a d : Fin 3, (a : ℕ) = 0 → d ≠ a →
      ((Finset.univ.filter fun b : Fin 3 => b ≠ d ∧ (registered ++ [[0, 1, 2]]).length <
        2 * (Finset.univ.filter fun j : Fin (registered ++ [[0, 1, 2]]).length =>
          (voteOrder (m := 3) (registered ++ [[0, 1, 2]])[j]).lt d b).card).card : ℚ) + 1 ≤
        (Finset.univ.filter fun b : Fin 3 => b ≠ a ∧ (registered ++ [[0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin (registered ++ [[0, 1, 2]]).length =>
            (voteOrder (m := 3) (registered ++ [[0, 1, 2]])[j]).lt a b).card).card := by
    decide +kernel
  have hties : ∀ a : Fin 3,
      (Finset.univ.filter fun b : Fin 3 => b ≠ a ∧
        ¬ (registered ++ [[0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin (registered ++ [[0, 1, 2]]).length =>
            (voteOrder (m := 3) (registered ++ [[0, 1, 2]])[j]).lt a b).card ∧
        ¬ (registered ++ [[0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin (registered ++ [[0, 1, 2]]).length =>
            (voteOrder (m := 3) (registered ++ [[0, 1, 2]])[j]).lt b a).card).card = 0 := by
    decide
  intro a d ha hda
  rw [hties a, hties d]
  have := h0 a d ha hda
  simp only [Nat.cast_zero, mul_zero, add_zero]
  exact lt_of_lt_of_le (lt_add_one _) this

/-- The decision problem accepts `yes` for representative `α = 0, 1/2, 1`, registering
`[[0, 1, 2]]`. -/
example :
    copelandConstructiveControlByAddingVotersDec 0 (bitEncode yes) = true ∧
      copelandConstructiveControlByAddingVotersDec (1 / 2) (bitEncode yes) = true ∧
      copelandConstructiveControlByAddingVotersDec 1 (bitEncode yes) = true := by
  have hf : ∀ α, CopelandConstructiveControlByAddingVotersFeasible α yes :=
    fun α => ⟨[[0, 1, 2]], by decide, by decide, winner_after α⟩
  simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, yes_wellFormed, hf]

/-- The parameter matters: with `α = 1` the decision problem rejects the well-formed instance
`no`, while with `α = 0` and `α = 1/2` it accepts `no` without registering anyone. -/
example :
    copelandConstructiveControlByAddingVotersDec 1 (bitEncode no) = false ∧
      copelandConstructiveControlByAddingVotersDec 0 (bitEncode no) = true ∧
      copelandConstructiveControlByAddingVotersDec (1 / 2) (bitEncode no) = true := by
  have h1 : ¬ CopelandConstructiveControlByAddingVotersFeasible 1 no := by
    rw [feasible_iff]
    unfold IsUniqueCopelandWinner copelandScore
    simp only [majority_iff]
    decide +kernel
  have hlow : ∀ α : ℚ, α = 0 ∨ α = 1 / 2 →
      CopelandConstructiveControlByAddingVotersFeasible α no := by
    rintro α (rfl | rfl) <;> refine ⟨[], by simp, by decide, ?_⟩ <;>
      unfold IsUniqueCopelandWinner copelandScore <;> simp only [majority_iff] <;> decide +kernel
  refine ⟨by simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, h1], ?_, ?_⟩
  · simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, no_wellFormed,
      hlow 0 (Or.inl rfl)]
  · have h2 := hlow (1 / 2) (Or.inr rfl)
    rw [one_div] at h2
    simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, no_wellFormed, h2]

/-- A candidate outside `0, 1, 2` is malformed. -/
example : copelandConstructiveControlByAddingVotersDec 0
    (bitEncode ((3, registered, [], 3, 0) : CondorcetConstructiveControlByAddingVotersInstance)) =
      false := by
  have hw : ¬ WellFormed
      ((3, registered, [], 3, 0) : CondorcetConstructiveControlByAddingVotersInstance) := by
    unfold WellFormed; decide
  simp [copelandConstructiveControlByAddingVotersDec, bitDecode_bitEncode, hw]

/-- A lone continuation bit is a truncated instance encoding, for every `α`. -/
example (α : ℚ) : copelandConstructiveControlByAddingVotersDec α [true] = false := by
  have h : bitDecode (α := CondorcetConstructiveControlByAddingVotersInstance) [true] = none := rfl
  simp [copelandConstructiveControlByAddingVotersDec, h]

end MetaMathlibExt.Complexity.NPComplete.CopelandConstructiveControlByAddingVoters
