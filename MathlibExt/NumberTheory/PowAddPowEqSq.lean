/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# The equation `2^x + 1 = z^2`

Lemma 1, case `n = 2`, of Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024), Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

From `(z - 1) (z + 1) = 2^x`, both factors are powers of `2` that
differ by `2`, so they are `2` and `4`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Lemma 1**, case `n = 2`: with `y = 0`, Equation
(1) `2^x + 1 = z^2` has the unique nonnegative
integer solution `(x, z) = (3, 3)`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1.
Proves `Wanted` entry `two_pow_add_one_eq_sq`. -/
theorem two_pow_add_one_eq_sq (x z : ℕ) :
    2 ^ x + 1 = z ^ 2 ↔ x = 3 ∧ z = 3 := by
  constructor
  · intro h
    have hx : 0 < 2 ^ x := Nat.two_pow_pos x
    have hz : 2 ≤ z := by
      rcases z with _ | _ | z
      · simp at h
      · simp at h
      · omega
    have hfac : (z - 1) * (z + 1) = 2 ^ x := by
      obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 := ⟨z - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      have : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
      omega
    obtain ⟨i, -, hi⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
    rcases i with _ | _ | i
    · rcases j with _ | j
      · simp only [pow_zero] at hj
        omega
      · rw [pow_succ] at hj
        omega
    · have hz3 : z = 3 := by
        simp only [zero_add, pow_one] at hi
        omega
      subst hz3
      refine ⟨Nat.pow_right_injective le_rfl ?_, rfl⟩
      simp only [Nat.reducePow] at h ⊢
      omega
    · rcases j with _ | _ | j
      · simp only [pow_zero] at hj
        omega
      · simp only [zero_add, pow_one] at hj
        omega
      · rw [pow_succ, pow_succ] at hi hj
        generalize 2 ^ i = a at hi
        generalize 2 ^ j = b at hj
        omega
  · rintro ⟨rfl, rfl⟩
    rfl

end MetaMathlibExt
