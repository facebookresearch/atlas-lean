/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HarmonicValuation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Basic

/-!
# Tests for the `2`-adic valuation of differences of harmonic numbers

* `weightedBinaryDigitSum`: the first values `0, 0, 2, 2, 8, 8, 10, 10, 24`
  quoted in the paper, checked by `decide`, and Theorem 4 at `n = 3, 4, 5`.
* Lengyel's results at small `m, n`, with `H_n - H_m` computed exactly by
  `norm_num` where this makes the valuation a concrete statement about a
  rational number: `ν₂(47 / 60) < 0` (Theorem 2), `ν₂(7 / 12) = -2`
  (Corollary 1), `ν₂(11 / 30) = -1` (Theorem 5), and both branches of
  Theorem 6 at `m = 3`, `n = 7, 8`. Also Corollary 1 at the endpoint
  `m = 2 ^ a` (`ν₂(H_8) = -3`), Lemma 1 at `n = 3`, and Theorem 5 at `n = 8`,
  where `⌊n / 2^r⌋ = 4` is even.
* Theorem 3 and Corollary 2 at `n = 6 = 2 + 4`.
* The helper lemmas on small inputs, including the empty interval in
  `padicValRat_two_harmonic_sub` and an unset bit in
  `card_filter_sup_Ioc_padicValNat_two_eq`.
-/

@[expose] public section

namespace MetaMathlibExtTest.HarmonicValuation

open MetaMathlibExt

/-! ### The weighted binary digit sum -/

/-- The first nine values displayed in the paper. -/
example : (List.range 9).map weightedBinaryDigitSum =
    [0, 0, 2, 2, 8, 8, 10, 10, 24] := by
  decide

example : weightedBinaryDigitSum 6 = 10 := by decide

/-- Theorem 4 at `n = 3, 4, 5`, checked against `decide`. -/
example : weightedBinaryDigitSum 6 = 2 * weightedBinaryDigitSum 3 + 6 ∧
    weightedBinaryDigitSum 7 = weightedBinaryDigitSum 6 := by
  decide

example : weightedBinaryDigitSum 8 = 2 * weightedBinaryDigitSum 4 + 8 ∧
    weightedBinaryDigitSum 9 = weightedBinaryDigitSum 8 :=
  weightedBinaryDigitSum_recurrence 4

example : weightedBinaryDigitSum 10 = 26 := by
  rw [(weightedBinaryDigitSum_recurrence 5).1]
  decide

/-- The sum defining `weightedBinaryDigitSum` may run past `Nat.log 2 n`. -/
example : weightedBinaryDigitSum 6 =
    ∑ i ∈ Finset.range 10, if Nat.testBit 6 i then i * 2 ^ i else 0 :=
  weightedBinaryDigitSum_eq_sum_range (by norm_num)

example : ∑ i ∈ Finset.range 4, (if Nat.testBit 13 i then 2 ^ i else 0) = 13 :=
  sum_range_testBit_two_pow (by norm_num)

/-! ### Harmonic differences -/

theorem harmonic_four_sub_two : harmonic 4 - harmonic 2 = 7 / 12 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem harmonic_five_sub_two : harmonic 5 - harmonic 2 = 47 / 60 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem harmonic_six_sub_four : harmonic 6 - harmonic 4 = 11 / 30 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem harmonic_seven_sub_four : harmonic 7 - harmonic 4 = 107 / 210 := by
  norm_num [harmonic, Finset.sum_range_succ]

theorem harmonic_eight_sub_five : harmonic 8 - harmonic 5 = 73 / 168 := by
  norm_num [harmonic, Finset.sum_range_succ]

/-! ### Lengyel's results -/

/-- Theorem 2: `1/3 + 1/4 + 1/5 = 47/60` is not a `2`-adic integer. -/
example : padicValRat 2 (47 / 60) < 0 := by
  rw [← harmonic_five_sub_two]
  exact padicValRat_two_harmonic_sub_neg 2 5 (by norm_num)

/-- Corollary 1 at `a = 2`, `m = 2`: `ν₂(1/3 + 1/4) = -2`. -/
example : padicValRat 2 (7 / 12) = -2 := by
  rw [← harmonic_four_sub_two]
  exact padicValRat_two_harmonic_pow_sub 2 2 (by norm_num) (by norm_num)

/-- Corollary 1 at the endpoint `m = 2 ^ a`, where `H_{n - m} = H_0`. -/
example : padicValRat 2 (harmonic 8) = -3 := by
  have := padicValRat_two_harmonic_pow_sub 3 8 (by norm_num) (by norm_num)
  rw [show (2 : ℕ) ^ 3 - 8 = 0 from rfl, harmonic_zero, sub_zero,
    show (2 : ℕ) ^ 3 = 8 from rfl] at this
  exact_mod_cast this

/-- Lemma 1 at `n = 3`: `ν₂(H_6 - H_3) = -⌊log₂ 6⌋ = -2`. -/
example : padicValRat 2 (harmonic 6 - harmonic 3) = -2 := by
  rw [padicValRat_two_harmonic_two_mul_sub 3 (by norm_num)]
  have : Nat.log 2 (2 * 3) = 2 := by decide
  rw [this]
  rfl

/-- Theorem 5 at `r = 1`, `n = 6`: `ν₂(1/5 + 1/6) = -1 - ν₂(3) = -1`. -/
example : padicValRat 2 (11 / 30) = -1 := by
  rw [← harmonic_six_sub_four]
  have := padicValRat_two_harmonic_sub_pow 1 6 (by norm_num)
  rw [show (6 / 2 ^ 1 : ℕ).factorization 2 = 0 from
    Nat.factorization_eq_zero_of_not_dvd (by decide)] at this
  exact this

/-- Theorem 5 at `r = 1`, `n = 8`, where `⌊n / 2^r⌋ = 4` is even:
`ν₂(1/7 + 1/8) = -1 - 2 = -3`. -/
example : padicValRat 2 (harmonic 8 - harmonic 6) = -3 := by
  rw [show (6 : ℕ) = 8 - 2 ^ 1 from rfl, padicValRat_two_harmonic_sub_pow 1 8
    (by norm_num), Nat.factorization_def _ Nat.prime_two,
    show (8 / 2 ^ 1 : ℕ) = 2 ^ 2 from rfl, padicValNat.prime_pow]
  rfl

/-- Theorem 6, first branch, at `m = 3`, `n = 7`: here `M = 2`, `j = 1`, and
`ν₂(1/5 + 1/6 + 1/7) = -M + 1 = -1`. -/
example : padicValRat 2 (107 / 210) = -1 := by
  have hM : Nat.clog 2 (3 + 1) = 2 := by decide
  have := (padicValRat_two_harmonic_sub_piecewise 3 7 (by norm_num)
    (by norm_num)).1
  rw [hM] at this
  rw [← harmonic_seven_sub_four, this (by norm_num)]
  rfl

/-- Theorem 6, second branch, at `m = 3`, `n = 8`: here `M = 2`, `j = 1`, and
`ν₂(1/6 + 1/7 + 1/8) = -M - ν₂(2) = -3`. -/
example : padicValRat 2 (73 / 168) = -3 := by
  have hM : Nat.clog 2 (3 + 1) = 2 := by decide
  have := (padicValRat_two_harmonic_sub_piecewise 3 8 (by norm_num)
    (by norm_num)).2
  rw [hM] at this
  rw [← harmonic_eight_sub_five, this (by norm_num),
    show (8 - 3) / 2 ^ 2 + 1 = 2 from rfl,
    Nat.Prime.factorization_self Nat.prime_two]
  rfl

/-- Theorem 3 at `n = 6 = 2^1 + 2^2`: two of `ν₂(H_6 - H_m)`, `m < 6`, equal
`-1` and four equal `-2`. -/
example : ((Finset.range 6).filter
    (fun m => padicValRat 2 (harmonic 6 - harmonic m) = -(1 : ℕ))).card =
    2 :=
  card_filter_padicValRat_two_harmonic_sub 6 1 (by decide)

example : ((Finset.range 6).filter
    (fun m => padicValRat 2 (harmonic 6 - harmonic m) = -(2 : ℕ))).card =
    4 :=
  card_filter_padicValRat_two_harmonic_sub 6 2 (by decide)

/-- Corollary 2 at `n = 6`: the six valuations sum to `-a(6) = -10`. -/
example : ∑ m ∈ Finset.range 6, padicValRat 2 (harmonic 6 - harmonic m) =
    -10 := by
  rw [sum_padicValRat_two_harmonic_sub]
  decide

/-! ### Helper lemmas -/

example : ¬ ∃ k ∈ Finset.Ioc 5 7, 4 ∣ k := by
  rw [exists_mem_Ioc_dvd_iff (by norm_num)]
  decide

example : 2 ≤ (Finset.Ioc 5 9).sup (padicValNat 2) := by
  rw [le_sup_Ioc_padicValNat_iff Nat.prime_two (by norm_num)]
  decide

/-- The only multiple of `3 ^ 2` in `(10, 20]` is `9 * 2 = 18`. -/
example : (Finset.Ioc 10 20).sup (padicValNat 3) = 2 := by
  rw [sup_Ioc_padicValNat_eq (r := 2) (c := 2) Nat.prime_three
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by decide)]

example : (Finset.Ioc 10 20).sup (padicValNat 3) = 2 := by
  rw [sup_Ioc_padicValNat_eq_iff Nat.prime_three (by norm_num)]
  decide

example : (Finset.Ioc 4 6).sup (padicValNat 2) ≠ padicValNat 2 7 :=
  sup_Ioc_padicValNat_two_ne (by norm_num)

/-- Bit `0` of `6` is not set, so no `m < 6` has maximum `0`. -/
example : ((Finset.range 6).filter
    (fun m => (Finset.Ioc m 6).sup (padicValNat 2) = 0)).card = 0 := by
  rw [card_filter_sup_Ioc_padicValNat_two_eq]
  decide

example : ∑ m ∈ Finset.range 6, (Finset.Ioc m 6).sup (padicValNat 2) = 10 := by
  rw [sum_range_sup_Ioc_padicValNat_two]
  decide

example : harmonic 3 < harmonic 4 := harmonic_strictMono (by norm_num)

/-- The empty interval: `ν₂(H_n - H_n) = ν₂(0) = 0`. -/
example (n : ℕ) : padicValRat 2 (harmonic n - harmonic n) = 0 := by
  rw [padicValRat_two_harmonic_sub n n le_rfl, Finset.Ioc_self,
    Finset.sup_empty]
  rfl

/-! ### Axioms -/

#print axioms weightedBinaryDigitSum_two
#print axioms weightedBinaryDigitSum_four
#print axioms sum_range_testBit_two_pow
#print axioms weightedBinaryDigitSum_eq_sum_range
#print axioms exists_mem_Ioc_dvd_iff
#print axioms le_sup_Ioc_padicValNat_iff
#print axioms sup_Ioc_padicValNat_eq_iff
#print axioms sup_Ioc_padicValNat_eq
#print axioms sup_Ioc_padicValNat_two_ne
#print axioms card_filter_sup_Ioc_padicValNat_two_eq
#print axioms sum_range_sup_Ioc_padicValNat_two
#print axioms harmonic_strictMono
#print axioms padicValRat_two_harmonic_sub
#print axioms padicValRat_two_harmonic_sub_neg
#print axioms card_filter_padicValRat_two_harmonic_sub
#print axioms padicValRat_two_harmonic_two_mul_sub
#print axioms padicValRat_two_harmonic_pow_sub
#print axioms sum_padicValRat_two_harmonic_sub
#print axioms weightedBinaryDigitSum_recurrence
#print axioms padicValRat_two_harmonic_sub_pow
#print axioms padicValRat_two_harmonic_sub_piecewise

end MetaMathlibExtTest.HarmonicValuation
