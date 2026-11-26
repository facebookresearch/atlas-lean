/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import MathlibExt.GroupTheory.RankAnalogueMaximalClassKourovka16Problem103

namespace MathlibExt.GroupTheory.RankAnalogueMaximalClassKourovka16Problem103Wanted

example : minGenerators (⊥ : Subgroup (Multiplicative (ZMod 2))) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold minGenerators
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨∅, rfl, by simp⟩

example : groupRank (Multiplicative (ZMod 1)) = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold groupRank
  apply csSup_le'
  rintro _ ⟨H, rfl⟩
  unfold minGenerators
  apply csInf_le (OrderBot.bddBelow _)
  exact ⟨∅, rfl, by simp [Subsingleton.elim H ⊥]⟩

example : HasCyclicLowerCentralFactorsFromSecond (Multiplicative (ZMod 2)) := by
  intro j hj
  let H : Subgroup (Multiplicative (ZMod 2)) := ⊤
  have h₁ : H.lowerCentralSeries 1 = ⊥ :=
    Subgroup.lowerCentralSeries_one_eq_bot_iff.mpr inferInstance
  have hbot : H.lowerCentralSeries j = ⊥ :=
    le_antisymm (h₁ ▸ H.lowerCentralSeries_antitone hj) bot_le
  refine ⟨1, Subgroup.one_mem _, fun x hx ↦ ⟨0, ?_⟩⟩
  change x ∈ H.lowerCentralSeries j at hx
  rw [hbot, Subgroup.mem_bot] at hx
  simp [hx]

example (r : ℕ) :
    ¬ (∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P →
      (∃ x y : P, Subgroup.closure ({x, y} : Set P) = ⊤) →
      HasCyclicLowerCentralFactorsFromSecond P →
      ∃ N : Subgroup P, ∃ _ : N.Normal, N.lowerCentralSeries 2 = ⊥ ∧ groupRank (P ⧸ N) ≤ r) :=
  fun h ↦ rankAnalogueMaximalClass_refuted ⟨2, Nat.prime_two, r, h⟩

end MathlibExt.GroupTheory.RankAnalogueMaximalClassKourovka16Problem103Wanted
