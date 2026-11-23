/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Reverse divisors with quotient four

If `n` is positive and its decimal reversal is `4 * n`, the outer digits of `n` are `2` and `8`.
Then `5 * n` begins with `1`, so its reversal is odd and cannot be divisible by `n`.
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

/-- In a block of `k + 1` digits, the units digit becomes the coefficient of `10 ^ k`
after reversal, including when that coefficient is zero. -/
private theorem reverse_div_place {digits : List ℕ} {k : ℕ} (hlen : digits.length = k + 1)
    (hd : ∀ d ∈ digits, d < 10) :
    Nat.ofDigits 10 digits.reverse / 10 ^ k = Nat.ofDigits 10 digits % 10 := by
  cases digits with
  | nil => simp at hlen
  | cons d ds =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    subst k
    have hbound := Nat.ofDigits_lt_base_pow_length (l := ds.reverse) (by decide : 1 < 10)
      (fun i hi => hd i (List.mem_cons_of_mem _ (List.mem_reverse.mp hi)))
    rw [List.length_reverse] at hbound
    rw [Nat.ofDigits_reverse_cons, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hbound, Nat.ofDigits_cons]
    simp [Nat.mod_eq_of_lt (hd d (by simp))]

/-- The two outer digits exchange places when read in reverse. -/
private theorem reverse_outer_digits {n k : ℕ} (hlen : (Nat.digits 10 n).length = k + 1) :
    Nat.reverseDigits 10 n / 10 ^ k = n % 10 ∧
      Nat.reverseDigits 10 n % 10 = n / 10 ^ k := by
  have hd : ∀ d ∈ Nat.digits 10 n, d < 10 := fun _ => Nat.digits_lt_base (by decide)
  constructor
  · simpa only [Nat.reverseDigits, Nat.ofDigits_digits] using reverse_div_place hlen hd
  · have hrev := reverse_div_place (hlen := List.length_reverse.trans hlen)
      (fun d hi => hd d (List.mem_reverse.mp hi))
    simpa only [Nat.reverseDigits, List.reverse_reverse, Nat.ofDigits_digits] using hrev.symm

/-- **Reverse divisors with quotient $4$ lack property $P^*$.** If $n > 0$ is a natural number
whose decimal reversal equals $4n$, then $n$ does not have the property $P^*$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Lemma 1. -/
theorem not_hasPropertyPStar_of_quotient_four (n : ℕ)
    (hn : 0 < n) (h : Nat.reverseDigits 10 n = 4 * n) :
    ¬ HasPropertyPStar n := by
  intro hP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
    (by simpa [List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero] using hn.ne' :
      (Nat.digits 10 n).length ≠ 0)
  let p := 10 ^ k
  have hp : 0 < p := Nat.pow_pos (by decide)
  obtain ⟨hunits, hlead⟩ := reverse_outer_digits hk
  rw [h] at hunits hlead
  change 4 * n / p = n % 10 at hunits
  change 4 * n % 10 = n / p at hlead
  -- The leading digit of `n` is even and at most two.
  have hlo : p ≤ n := (Nat.lt_digits_length_iff (by decide) n).mp (by omega)
  have hhi : 4 * n < 10 * p := (Nat.div_lt_iff_lt_mul hp).mp (by omega)
  have hpos : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hlo)
  have hsmall : n / p < 3 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega)
  have htwo : n / p = 2 := by omega
  have hlow : 2 * p ≤ n := (Nat.le_div_iff_mul_le hp).mp htwo.ge
  -- Thus `4 * n` begins with at least eight, and the units digit of `n` is eight.
  have height : 8 ≤ 4 * n / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  have heven : 2 ∣ n := by omega
  -- The multiple `5 * n` has one more digit and begins with one.
  have hnext : 10 ^ (k + 1) = 10 * p := by rw [pow_succ']
  have hlen : (Nat.digits 10 (5 * n)).length = (k + 1) + 1 := by
    have hl := (Nat.lt_digits_length_iff (by decide : 1 < 10) (5 * n) (k := k + 1)).mpr
      (by rw [hnext]; omega)
    have hu := (Nat.digits_length_le_iff (by decide : 1 < 10) (5 * n) (k := (k + 1) + 1)).mpr
      (by rw [pow_succ, hnext]; omega)
    omega
  have hone : 5 * n / 10 ^ (k + 1) = 1 := by
    apply Nat.div_eq_of_lt_le <;> rw [hnext] <;> omega
  have hodd := (reverse_outer_digits hlen).2.trans hone
  have hdvd := heven.trans (hP (5 * n) (dvd_mul_left n 5))
  omega

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
