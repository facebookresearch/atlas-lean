/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-!
# Congruence lemmas for three consecutive powerful numbers

Lemmas 1–3 of Tsz Ho Chan, "A Note on Three Consecutive Powerful
Numbers", *INTEGERS* 25 (2025), Paper A7, DOI 10.5281/zenodo.14679327
(<https://math.colgate.edu/~integers/z7/z7.pdf>).

The paper's exact-divisibility notation `3 ∥ N` is spelled out as
`3 ∣ N ∧ ¬ 9 ∣ N`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Lemma 1**: the difference of two integer squares is never `2`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 1.
Proves `Wanted` entry `int_sq_sub_int_sq_ne_two`. -/
theorem int_sq_sub_int_sq_ne_two
    (a b : ℤ) :
    a ^ 2 - b ^ 2 ≠ 2 := by
  intro h
  have h4 := congrArg (· % 4) h
  rcases (by omega : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3)
      with ha | ha | ha | ha <;>
    rcases (by omega : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3)
        with hb | hb | hb | hb <;>
    simp [pow_two, Int.sub_emod, Int.mul_emod, ha, hb] at h4

/-- **Lemma 2**: if `x ≡ 1 (mod 3)`, then `3` exactly divides
`x^2 + x + 1`, in the sense `3 ∣ x^2 + x + 1` but
`¬ 9 ∣ x^2 + x + 1`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 2.
Proves `Wanted` entry `three_exact_dvd_sq_add_self_add_one`. -/
theorem three_exact_dvd_sq_add_self_add_one
    (x : ℤ) (hx : x % 3 = 1) :
    3 ∣ x ^ 2 + x + 1 ∧ ¬ 9 ∣ x ^ 2 + x + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 3 * k + 1 := ⟨x / 3, by omega⟩
  have e : (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 9 * (k ^ 2 + k) + 3 := by
    ring
  rw [e]
  omega

/-- **Lemma 3**: if `x ≡ 2 (mod 3)`, then `3` exactly divides
`x^2 - x + 1`, in the sense `3 ∣ x^2 - x + 1` but
`¬ 9 ∣ x^2 - x + 1`.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 3.
Proves `Wanted` entry `three_exact_dvd_sq_sub_self_add_one`. -/
theorem three_exact_dvd_sq_sub_self_add_one
    (x : ℤ) (hx : x % 3 = 2) :
    3 ∣ x ^ 2 - x + 1 ∧ ¬ 9 ∣ x ^ 2 - x + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 3 * k + 2 := ⟨x / 3, by omega⟩
  have e : (3 * k + 2) ^ 2 - (3 * k + 2) + 1 = 9 * (k ^ 2 + k) + 3 := by
    ring
  rw [e]
  omega

end MetaMathlibExt
