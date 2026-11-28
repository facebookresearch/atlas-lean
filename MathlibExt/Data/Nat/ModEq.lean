/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.ModEq

/-!
# Congruences of natural numbers

Multiplication by two has the inverse `(q + 1) / 2` modulo an odd natural `q`.

## References

* The proof comes from `double_iff` in `MathlibExt.NumberTheory.PalindromesArithmeticProgressions`.
-/

/-- **Inverting doubling modulo an odd modulus.**

For odd `q`, a natural number `x` satisfies `2 * x ≡ r [MOD q]` exactly when
`x ≡ ((q + 1) / 2) * r [MOD q]`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, Theorem 9,
proof of the odd-modulus case of (19). -/
public theorem Nat.two_mul_modEq_iff_of_odd {q : ℕ} (hq : Odd q) (x r : ℕ) :
    2 * x ≡ r [MOD q] ↔ x ≡ ((q + 1) / 2) * r [MOD q] := by
  let u := (q + 1) / 2
  have hu : u * 2 ≡ 1 [MOD q] := by
    have h : u * 2 = 1 + q := by obtain ⟨k, hk⟩ := hq; dsimp [u]; omega
    rw [h, Nat.add_modulus_modEq_iff]
  constructor
  · intro h
    exact (by simpa [mul_assoc] using hu.symm.mul_right x :
      x ≡ u * (2 * x) [MOD q]).trans (h.mul_left u)
  · intro h
    apply (h.mul_left 2).trans
    simpa [u, mul_left_comm, mul_assoc, mul_comm] using hu.mul_right r
