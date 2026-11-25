/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PermutationCharacterGenerationKourovka12Problem79
import Mathlib.Tactic.NormNum

open MathlibExt.GroupTheory.PermutationCharacterGenerationKourovka12Problem79Wanted

-- At the identity the regular character counts all elements, including the infinite-card case.
private theorem regular_at_one (G : Type*) [Group G] :
    permChar (⊥ : Subgroup G) 1 = (Nat.card G : ℂ) := by
  unfold permChar
  congr 1
  let e := Equiv.subtypeUnivEquiv (fun q : G ⧸ (⊥ : Subgroup G) => one_smul G q)
  exact Nat.card_congr (e.trans QuotientGroup.quotientBot.toEquiv)

example : permChar (⊥ : Subgroup (Multiplicative ℤ)) 1 = 0 := by
  simp [regular_at_one]

-- In the group of order two, taking both elements to be the identity gives negative degree.
example : strunkovFunction (1 : Multiplicative (Fin 2)) 1 1 = -2 := by
  rw [strunkovFunction, one_mul, Subgroup.zpowers_one_eq_bot, regular_at_one,
    Nat.card_eq_fintype_card]
  norm_num

-- The proved refutation supplies a character witness with proper generated subgroup.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (a b : G),
    IsCharacter (strunkovFunction a b) ∧ Subgroup.closure {a, b} ≠ ⊤ := by
  by_contra! h
  exact strunkovCharacterImpliesGeneration_refuted fun G group finite a b hc =>
    h G group finite a b hc
