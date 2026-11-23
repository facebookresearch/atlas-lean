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
