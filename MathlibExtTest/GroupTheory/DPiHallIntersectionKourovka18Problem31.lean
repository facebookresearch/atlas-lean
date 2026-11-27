/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the refutation of Kourovka 18.31

The negative answer, Zenkov's group as an explicit witness, and edge cases of the `π`-number,
Hall `π`-subgroup and `π`-core definitions.
-/

namespace MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted

/-- Kourovka 18.31 has a negative answer. -/
example : ¬ threeHallSubgroupsIntersectInCore := threeHallSubgroupsIntersectInCore_refuted

/-- Zenkov's group witnesses the negative answer: it is a `D_π`-group for `π = {3, 13}`, and no
three of its Hall `{3, 13}`-subgroups meet in its `{3, 13}`-core. -/
example : IsDPiGroup {3, 13} Zenkov.group ∧
    ∀ H₁ H₂ H₃ : Subgroup Zenkov.group, IsHallPiSubgroup {3, 13} H₁ →
      IsHallPiSubgroup {3, 13} H₂ → IsHallPiSubgroup {3, 13} H₃ →
      H₁ ⊓ H₂ ⊓ H₃ ≠ piCore {3, 13} Zenkov.group :=
  ⟨Zenkov.isDPiGroup, fun _ _ _ h₁ h₂ h₃ =>
    Zenkov.piCore_eq_bot ▸ Zenkov.inf_inf_ne_bot_of_isHallPiSubgroup h₁ h₂ h₃⟩

/-- The order of Zenkov's group is `|L₂(27)| * 3 = 2 ^ 2 * 3 ^ 4 * 7 * 13`. -/
example : Nat.card Zenkov.group = 27 * (27 ^ 2 - 1) / 2 * 3 ∧
    Nat.card Zenkov.group = 2 ^ 2 * 3 ^ 4 * 7 * 13 := by
  simp only [Zenkov.card_group]
  norm_num

/-- The `{3, 13}`-core of Zenkov's group is trivial but the group is not: the core is proper. -/
example : piCore {3, 13} Zenkov.group ≠ ⊤ := by
  have : Nontrivial Zenkov.group :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [Zenkov.card_group]; norm_num)
  rw [Zenkov.piCore_eq_bot]
  exact bot_ne_top

/-- `1053 = 3 ^ 4 * 13` is a `{3, 13}`-number, while `28 = 2 ^ 2 * 7` is not. -/
example : IsPiNumber {3, 13} 1053 ∧ ¬ IsPiNumber {3, 13} 28 := by
  refine ⟨fun p hp hdvd => ?_, fun h => absurd (h 2 Nat.prime_two (by norm_num)) (by simp)⟩
  rw [show (1053 : ℕ) = 3 ^ 4 * 13 by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h13
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h3))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h13)

/-- Every set of primes accepts `1`, but `0` (the order of an infinite subgroup) is a `π`-number
only when `π` contains every prime. -/
example (π : Set ℕ) : IsPiNumber π 1 ∧ ¬ IsPiNumber {3, 13} 0 :=
  ⟨fun _ hp h => absurd (Nat.eq_one_of_dvd_one h) hp.one_lt.ne',
    fun h => absurd (h 2 Nat.prime_two (dvd_zero 2)) (by simp)⟩

/-- In a finite group, the whole group is a maximal Hall `π`-subgroup when `π` contains every prime,
and the trivial subgroup is a Hall `∅`-subgroup. -/
example (G : Type) [Group G] [Finite G] :
    IsHallPiSubgroup {p | p.Prime} (⊤ : Subgroup G) ∧
    IsMaximalPiSubgroup {p | p.Prime} (⊤ : Subgroup G) ∧ IsHallPiSubgroup ∅ (⊥ : Subgroup G) := by
  have htop : IsPiSubgroup {p | p.Prime} (⊤ : Subgroup G) := fun _ hp _ => hp
  refine ⟨⟨htop, fun p hp h => ?_⟩, ⟨htop, fun K _ hK => top_le_iff.mp hK⟩, ⟨?_, fun _ _ _ => id⟩⟩
  · rw [Subgroup.index_top] at h
    exact absurd (Nat.eq_one_of_dvd_one h) hp.one_lt.ne'
  · intro p hp h
    rw [Subgroup.card_bot] at h
    exact absurd (Nat.eq_one_of_dvd_one h) hp.one_lt.ne'

/-- The `π`-core is trivial for `π = ∅`, and it is the whole group when `π` contains every prime
and the group is finite. -/
example (G : Type) [Group G] [Finite G] :
    piCore ∅ G = ⊥ ∧ piCore {p | p.Prime} G = ⊤ := by
  refine ⟨sSup_eq_bot.mpr fun N ⟨_, hN⟩ => ?_, top_le_iff.mp (le_sSup ⟨inferInstance,
    fun _ hp _ => hp⟩)⟩
  refine Subgroup.eq_bot_of_card_eq N ?_
  by_contra h1
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd h1
  exact hN p hp hpN

end MathlibExt.GroupTheory.DPiHallIntersectionKourovka18Problem31Wanted
