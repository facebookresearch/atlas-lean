/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Coprimality of integers with property $P^*$

Every positive integer sharing a factor with ten has a multiple whose decimal reversal
is coprime to ten, so it lacks property $P^*$.
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- **Positive integers sharing a factor with $10$ lack property $P^*$.** If $n \ge 1$ is a
natural number with $\gcd(n, 10) \ne 1$, then $n$ does not have the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 2. -/
theorem not_hasPropertyPStar_of_not_coprime (n : ℕ)
    (hn : 1 ≤ n) (h : ¬ Nat.Coprime n 10) :
    ¬ HasPropertyPStar n := by
  intro hP
  -- The first multiple of n above 10 ^ k has the form 10 ^ k + r with r < 10 ^ k.
  let k := (Nat.digits 10 n).length
  let r := n - 10 ^ k % n
  have hr : r < 10 ^ k :=
    (Nat.sub_le _ _).trans_lt (Nat.lt_base_pow_length_digits (by decide : 1 < 10))
  have hdvd : n ∣ r + 10 ^ k := by
    refine ⟨10 ^ k / n + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mod_add_div (10 ^ k) n
    have := Nat.mod_lt (10 ^ k) hn
    dsimp [r]
    omega
  -- Pad the low block to k digits. The leading one becomes the units digit.
  let ds := Nat.digits 10 r ++ List.replicate (k - (Nat.digits 10 r).length) 0
  have hdigits : Nat.digits 10 (r + 10 ^ k) = ds ++ [1] := by
    have hlen := (Nat.digits_length_le_iff (by decide : 1 < 10) r).mpr hr
    simpa only [Nat.add_sub_of_le hlen, Nat.mul_one, show Nat.digits 10 1 = [1] by decide] using
      (Nat.digits_append_zeroes_append_digits (n := r) (k := k - (Nat.digits 10 r).length)
        (by decide : 1 < 10) (by decide : 0 < 1)).symm
  apply h
  apply Nat.Coprime.of_dvd_left (hP _ hdvd)
  rw [Nat.reverseDigits, hdigits]
  simp [Nat.ofDigits_cons]

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
