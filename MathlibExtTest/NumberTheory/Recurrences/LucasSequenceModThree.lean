/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasSequenceModThree

/-! # Regression tests for Lucas sequences modulo three -/

open MetaMathlibExt

private def qMultiple : LucasSequenceParams := ⟨-1, -3, by decide⟩
private def pMultiple : LucasSequenceParams := ⟨-6, 4, by decide⟩
private def qNegOne : LucasSequenceParams := ⟨2, -4, by decide⟩
private def qOne : LucasSequenceParams := ⟨-2, -2, by decide⟩

example : ∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n →
    lucasU qMultiple (n + k) ≡ lucasU qMultiple n [ZMOD 3] :=
  (lucasU_mod_three qMultiple (by decide)).1

example (n : ℕ) (hn : 1 ≤ n) : ¬ 3 ∣ lucasU qMultiple n :=
  (lucasU_mod_three qMultiple (by decide)).2.1 (by decide) n hn

-- A positive-index period need not be a period at index zero.
example : ¬ ∃ k : ℕ, 0 < k ∧ ∀ n, lucasU qMultiple (n + k) ≡ lucasU qMultiple n [ZMOD 3] := by
  rintro ⟨k, hk, h⟩
  apply (lucasU_mod_three qMultiple (by decide)).2.1 (by decide) k hk
  apply Int.modEq_zero_iff_dvd.mp
  simpa only [Nat.zero_add, lucasU] using h 0

-- The hypothesis excludes a common factor of three, not all common factors.
example (n : ℕ) : 3 ∣ lucasU pMultiple n ↔ 2 ∣ n :=
  (lucasU_mod_three pMultiple (by decide)).2.2.1 (by decide) n

example (n : ℕ) : 3 ∣ lucasU qNegOne n ↔ 4 ∣ n :=
  (lucasU_mod_three qNegOne (by decide)).2.2.2.1 (by decide) (by decide) n

example : (∀ n, 3 ∣ lucasU qOne n ↔ 3 ∣ n) ∧ 3 ∣ qOne.p ^ 2 - 4 * qOne.q :=
  (lucasU_mod_three qOne (by decide)).2.2.2.2 (by decide) (by decide)
