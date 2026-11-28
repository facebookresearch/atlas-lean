/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Base digits of a quotient

Dividing by a power of the base removes low-order digits from the little-endian expansion.

## References

* The digit-division proof is from `MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase`.
-/

namespace Nat

private theorem last_drop_ne_zero (b n t : ℕ) (h : (b.digits n).drop t ≠ []) :
    ((b.digits n).drop t).getLast h ≠ 0 := by
  have hn : n ≠ 0 := by
    intro hn
    simp [hn] at h
  have H := Nat.getLast_digit_ne_zero b hn
  have he : (b.digits n).take t ++ (b.digits n).drop t = b.digits n := List.take_append_drop ..
  simpa only [← List.getLast_append_of_right_ne_nil ((b.digits n).take t) _ h, he] using H

/-- For `b ≥ 2`, the little-endian base-`b` expansion of `n / b ^ t` is the expansion
of `n` with its first `t` entries dropped. -/
public theorem digits_div_pow {b : ℕ} (hb : 2 ≤ b) (n t : ℕ) :
    b.digits (n / b ^ t) = (b.digits n).drop t := by
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ hb]
  exact Nat.digits_ofDigits b hb _ (fun _ hx => Nat.digits_lt_base hb (List.mem_of_mem_drop hx))
    (last_drop_ne_zero b n t)

end Nat
