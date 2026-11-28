/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BanksWinnerDefs

namespace MetaMathlibExt.Complexity.NPComplete.BanksWinner

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Feasibility unfolded into bounded quantifiers over vertex sets. -/
private theorem feasible_iff (i : BanksWinnerInstance) :
    BanksWinnerFeasible i ↔ ∃ X : Finset (Fin i.1),
      ((∀ a ∈ X, ∀ b ∈ X, ∀ d ∈ X, ((a : ℕ), (b : ℕ)) ∈ i.2.1 → ((b : ℕ), (d : ℕ)) ∈ i.2.1 →
          ((a : ℕ), (d : ℕ)) ∈ i.2.1) ∧
        ∀ Y : Finset (Fin i.1), (∀ a ∈ Y, ∀ b ∈ Y, ∀ d ∈ Y, ((a : ℕ), (b : ℕ)) ∈ i.2.1 →
          ((b : ℕ), (d : ℕ)) ∈ i.2.1 → ((a : ℕ), (d : ℕ)) ∈ i.2.1) → X ⊆ Y → Y ⊆ X) ∧
      ∃ c ∈ X, (c : ℕ) = i.2.2 ∧ ∀ v ∈ X, v ≠ c → ((c : ℕ), (v : ℕ)) ∈ i.2.1 := by
  simp only [BanksWinnerFeasible, Maximal, IsTransitiveSet, Dominates]

/-- The cyclic tournament `0 → 1 → 2 → 0`. -/
private abbrev cyclic : BanksWinnerInstance := (3, [(0, 1), (1, 2), (2, 0)], 0)

/-- The transitive tournament `0 → 1`, `0 → 2`, `1 → 2`, asking about the bottom vertex `2`. -/
private abbrev transitive : BanksWinnerInstance := (3, [(0, 1), (0, 2), (1, 2)], 2)

set_option synthInstance.maxSize 8192 in
/-- The decision problem accepts the cyclic tournament: `{0, 1}` is a maximal transitive set
with top vertex `0`. -/
example : banksWinnerDec (bitEncode cyclic) = true := by
  have hw : WellFormed cyclic := by unfold WellFormed; decide
  have hf : BanksWinnerFeasible cyclic := by
    rw [feasible_iff]
    dsimp only [cyclic]
    exact ⟨{0, 1}, by decide, 0, by decide, rfl, by decide⟩
  simp [banksWinnerDec, bitDecode_bitEncode, hw, hf]

set_option synthInstance.maxSize 8192 in
/-- The decision problem rejects the well-formed transitive tournament with `c = 2`: the only
maximal transitive set is the whole vertex set, whose top vertex is `0`. -/
example : WellFormed transitive ∧ banksWinnerDec (bitEncode transitive) = false := by
  have hf : ¬ BanksWinnerFeasible transitive := by
    rw [feasible_iff]
    dsimp only [transitive]
    decide
  exact ⟨by unfold WellFormed; decide, by simp [banksWinnerDec, bitDecode_bitEncode, hf]⟩

set_option synthInstance.maxSize 8192 in
/-- A pair of opposite arcs is malformed, although `{0}` is then a maximal transitive set with
top vertex `0`. -/
example :
    BanksWinnerFeasible ((2, [(0, 1), (1, 0)], 0) : BanksWinnerInstance) ∧
      banksWinnerDec (bitEncode ((2, [(0, 1), (1, 0)], 0) : BanksWinnerInstance)) = false := by
  have hw : ¬ WellFormed ((2, [(0, 1), (1, 0)], 0) : BanksWinnerInstance) := by
    unfold WellFormed; decide
  refine ⟨?_, by simp [banksWinnerDec, bitDecode_bitEncode, hw]⟩
  rw [feasible_iff]
  dsimp only
  exact ⟨{0}, by decide, 0, by decide, rfl, by decide⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : banksWinnerDec [true] = false := by
  have h : bitDecode (α := BanksWinnerInstance) [true] = none := rfl
  simp [banksWinnerDec, h]

end MetaMathlibExt.Complexity.NPComplete.BanksWinner
