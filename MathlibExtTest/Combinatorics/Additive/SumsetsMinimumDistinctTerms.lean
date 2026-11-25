/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SumsetsMinimumDistinctTerms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open Finset MetaMathlibExt
open scoped Pointwise

-- The subset size can share a factor with the modulus.
example (ℓ : ZMod 6) : ∃ a b : ZMod 6, a ≠ b ∧ a + b = ℓ := by
  obtain ⟨L, hcard, hsum⟩ := exists_card_eq_sum_eq_zmod 6 2 (by decide) (by decide) ℓ
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hcard
  exact ⟨a, b, hab, by simpa [hab] using hsum⟩

-- At the upper endpoint every residue is realized by omitting a single element.
example (n : ℕ) (ℓ : ZMod (n + 2)) :
    ∃ a : ZMod (n + 2), (univ.erase a).sum id = ℓ := by
  obtain ⟨L, hcard, hsum⟩ := exists_card_eq_sum_eq_zmod (n + 2) (n + 1) (by omega) (by omega) ℓ
  have hcompl : Lᶜ.card = 1 := by rw [card_compl, ZMod.card, hcard]; omega
  obtain ⟨a, ha⟩ := card_eq_one.mp hcompl
  exact ⟨a, by simpa [← compl_singleton, ← ha] using hsum⟩

-- Below the cap, the theorem gives the linear growth bound.
example : 4 ≤ (3 • ({0, 1} : Finset (ZMod 5))).card := by
  exact cauchy_davenport_nsmul Nat.prime_five ({0, 1} : Finset (ZMod 5))
    (by decide) 3 (by decide)

-- At the smallest prime, the cap persists after it has already been reached.
example : (3 • ({0, 1} : Finset (ZMod 2))).card = 2 := by
  apply Nat.le_antisymm
  · exact (card_le_univ (s := 3 • ({0, 1} : Finset (ZMod 2)))).trans_eq (ZMod.card 2)
  · exact cauchy_davenport_nsmul Nat.prime_two ({0, 1} : Finset (ZMod 2))
      (by decide) 3 (by decide)

-- Both the summand size and the number of summands can be two.
example : (({0, 1} : Finset (ZMod 5)) : Set (ZMod 5)).IsAPOfLength 2 := by
  exact vosper_nsmul Nat.prime_five {0, 1} (by decide) 2 (by decide) (by decide) (by decide)

-- A fourfold sumset of a progression wrapping around zero attains the p - 2 boundary.
example : (({9, 0, 2} : Finset (ZMod 11)) : Set (ZMod 11)).IsAPOfLength 3 := by
  exact vosper_nsmul (by decide) {9, 0, 2} (by decide) 4 (by decide) (by decide) (by decide)
