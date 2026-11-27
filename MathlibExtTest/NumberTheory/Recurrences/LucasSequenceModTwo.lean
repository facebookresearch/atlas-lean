/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Recurrences.LucasSequenceModTwo

open MetaMathlibExt

private def oddEven : LucasSequenceParams := ⟨1, 2, by decide⟩
private def evenOdd : LucasSequenceParams := ⟨2, -1, by decide⟩
private def oddOdd : LucasSequenceParams := ⟨1, -1, by decide⟩

-- With even Q, index zero is exceptional and all positive indices are odd.
example : (2 : ℤ) ∣ lucasU oddEven 0 := by decide

example (n : ℕ) : ¬ (2 : ℤ) ∣ lucasU oddEven (n + 1) :=
  (lucasU_mod_two oddEven (by decide)).2.1 (by decide) (by decide) _ (Nat.succ_pos _)

example : ∃ k : ℕ, 0 < k ∧ ∀ n, 1 ≤ n → lucasU oddEven (n + k) ≡ lucasU oddEven n [ZMOD 2] :=
  (lucasU_mod_two oddEven (by decide)).1

-- With even P, the zero pattern includes index zero and the discriminant is even.
example : (2 : ℤ) ∣ lucasU evenOdd 0 ∧ (2 : ℤ) ∣ evenOdd.p ^ 2 - 4 * evenOdd.q := by
  obtain ⟨h, hD⟩ := (lucasU_mod_two evenOdd (by decide)).2.2.1 (by decide) (by decide)
  exact ⟨(h 0).mpr (dvd_zero _), hD⟩

example (n : ℕ) : (2 : ℤ) ∣ lucasU evenOdd n ↔ 2 ∣ n :=
  ((lucasU_mod_two evenOdd (by decide)).2.2.1 (by decide) (by decide)).1 n

-- For the Fibonacci parameters, precisely the multiples of three give even terms.
example (n : ℕ) : (2 : ℤ) ∣ lucasU oddOdd n ↔ 3 ∣ n :=
  (lucasU_mod_two oddOdd (by decide)).2.2.2 (by decide) (by decide) n
