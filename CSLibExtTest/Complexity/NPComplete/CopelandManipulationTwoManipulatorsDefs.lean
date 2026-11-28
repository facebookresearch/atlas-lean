/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CopelandManipulationTwoManipulatorsDefs
-- `List.mem_permutations'` reduces the manipulative votes to a finite search.
import Mathlib.Data.List.Permutation

namespace MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers supporters)
open BordaManipulationTwoManipulators (BordaManipulationInstance IsVote WellFormed)
open CondorcetConstructiveControlByAddingVoters (profile voteOrder)
open CopelandConstructiveControlByAddingVoters (copelandScore)

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

/-- The manipulative votes range over the permutations of the candidates. -/
private theorem feasible_iff (α : ℚ) (i : BordaManipulationInstance) :
    CopelandManipulationFeasible α i ↔ ∃ w₁ ∈ (List.range i.1).permutations',
      ∃ w₂ ∈ (List.range i.1).permutations', IsCopelandWinner α i.1 (i.2.1 ++ [w₁, w₂]) i.2.2 := by
  simp only [CopelandManipulationFeasible, IsVote, List.mem_permutations', exists_and_left]

/-- One vote `1 2 0`; two manipulators voting `0 1 2` make `0` beat both others. -/
private abbrev yes : BordaManipulationInstance := (3, [[1, 2, 0]], 0)

/-- Three votes `1 2 0`: `1` beats `0` and `2` whatever two manipulators vote. -/
private abbrev no : BordaManipulationInstance := (3, [[1, 2, 0], [1, 2, 0], [1, 2, 0]], 0)

/-- With an odd number of voters nobody ties, so `0` wins for every `α`. -/
private theorem yes_winner (α : ℚ) : IsCopelandWinner α 3 ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]) 0 := by
  unfold IsCopelandWinner copelandScore
  simp only [majority_iff]
  have hwins : ∀ a d : Fin 3, (a : ℕ) = 0 →
      (Finset.univ.filter fun b : Fin 3 => b ≠ d ∧ ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length <
        2 * (Finset.univ.filter fun j : Fin ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length =>
          (voteOrder (m := 3) ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]])[j]).lt d b).card).card ≤
        (Finset.univ.filter fun b : Fin 3 => b ≠ a ∧ ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length =>
            (voteOrder (m := 3) ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]])[j]).lt a b).card).card := by
    decide
  have hties : ∀ a : Fin 3,
      (Finset.univ.filter fun b : Fin 3 => b ≠ a ∧
        ¬ ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length =>
            (voteOrder (m := 3) ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]])[j]).lt a b).card ∧
        ¬ ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length <
          2 * (Finset.univ.filter fun j : Fin ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]]).length =>
            (voteOrder (m := 3) ([[1, 2, 0]] ++ [[0, 1, 2], [0, 1, 2]])[j]).lt b a).card).card = 0 := by
    decide
  intro a d ha
  rw [hties a, hties d]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  exact_mod_cast hwins a d ha

/-- The decision problem accepts `yes` for every `α`, in particular `α = 0, 1/2, 1`. -/
example (α : ℚ) : copelandManipulationDec α (bitEncode yes) = true := by
  have hw : WellFormed yes := by unfold WellFormed IsVote; decide
  have hf : CopelandManipulationFeasible α yes :=
    ⟨[0, 1, 2], [0, 1, 2], by unfold IsVote; decide, by unfold IsVote; decide, yes_winner α⟩
  simp [copelandManipulationDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed instance `no` at `α = 0, 1/2, 1`. -/
example :
    WellFormed no ∧ copelandManipulationDec 0 (bitEncode no) = false ∧
      copelandManipulationDec (1 / 2) (bitEncode no) = false ∧
      copelandManipulationDec 1 (bitEncode no) = false := by
  have hf : ∀ α : ℚ, α = 0 ∨ α = 1 / 2 ∨ α = 1 → ¬ CopelandManipulationFeasible α no := by
    rintro α (rfl | rfl | rfl) <;> rw [feasible_iff] <;>
      unfold IsCopelandWinner copelandScore <;> simp only [majority_iff] <;> decide +kernel
  have h0 := hf 0 (Or.inl rfl)
  have h2 := hf (1 / 2) (Or.inr (Or.inl rfl))
  have h1 := hf 1 (Or.inr (Or.inr rfl))
  rw [one_div] at h2
  exact ⟨by unfold WellFormed IsVote; decide, by simp [copelandManipulationDec, bitDecode_bitEncode, h0],
    by simp [copelandManipulationDec, bitDecode_bitEncode, h2],
    by simp [copelandManipulationDec, bitDecode_bitEncode, h1]⟩

/-- A candidate outside `0, 1, 2` is malformed. -/
example : copelandManipulationDec 0 (bitEncode ((3, [], 3) : BordaManipulationInstance)) =
    false := by
  have hw : ¬ WellFormed ((3, [], 3) : BordaManipulationInstance) := by
    unfold WellFormed IsVote; decide
  simp [copelandManipulationDec, bitDecode_bitEncode, hw]

/-- A lone continuation bit is a truncated instance encoding, for every `α`. -/
example (α : ℚ) : copelandManipulationDec α [true] = false := by
  have h : bitDecode (α := BordaManipulationInstance) [true] = none := rfl
  simp [copelandManipulationDec, h]

end MetaMathlibExt.Complexity.NPComplete.CopelandManipulationTwoManipulators
