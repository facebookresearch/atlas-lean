/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniqueness
import MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativePrimeOneModFour
import all MathlibExt.NumberTheory.ArithmeticFunction.ParallelogramSquareUniquenessParallelogramMultiplicativePrimeThreeModFour

/-!
# Parallelogram uniqueness of squares for multiplicative functions

A complex-valued multiplicative arithmetic function satisfying the parallelogram identity on
squares for all positive natural numbers `m > n`, with `f 4 ≠ 0`, takes the value `n ^ 2`
at every natural number `n`. At zero this is the defining convention for arithmetic functions.

## References

* Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative Functions*,
  INTEGERS 24 (2024), Article A108, pp. 1–8, Theorem 1, using Table 1 and Theorems 3–6.
* The prime induction reuses `parallelogram_multiplicative_sq_add_one` from
  `ParallelogramSquareUniqueness`, `parallelogram_multiplicative_prime_one_mod_four` from
  `ParallelogramSquareUniquenessParallelogramMultiplicativePrimeOneModFour`, and
  `parallelogram_multiplicative_prime_three_mod_four` and `smooth_eq_sq` from
  `ParallelogramSquareUniquenessParallelogramMultiplicativePrimeThreeModFour`.
-/

namespace MetaMathlibExt

open ArithmeticFunction

section

variable {f : ArithmeticFunction ℂ} (hf : f.IsMultiplicative)
variable (hpar : ∀ m n : ℕ, 0 < n → n < m →
  f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))

include hpar in
private theorem scaled_parallelogram (s m n : ℕ) (hs : 0 < s) (hn : 0 < n) (hm : n < m) :
    f (s ^ 2 * (m ^ 2 + n ^ 2)) + f (s ^ 2 * (m ^ 2 - n ^ 2)) =
      2 * f (s ^ 2 * m ^ 2) + 2 * f (s ^ 2 * n ^ 2) := by
  simpa only [mul_pow, ← mul_add, ← Nat.mul_sub] using
    hpar (s * m) (s * n) (Nat.mul_pos hs hn) (Nat.mul_lt_mul_of_pos_left hm hs)

include hf hpar in
private theorem two_pow_values (h2 : f 2 = 4) (h4 : f 4 = 16) (h8 : f 8 = 64) :
    ∀ r : ℕ, f (2 ^ r) = (2 : ℂ) ^ (2 * r) := by
  have e32 : f 13 + f 5 = 2 * f 9 + 2 * f 4 := hpar 3 2 (by decide) (by decide)
  have e31 : f 10 + f 8 = 2 * f 9 + 2 * f 1 := hpar 3 1 (by decide) (by decide)
  rw [show 10 = 2 * 5 by decide, hf.map_mul_of_coprime (by decide), h2, h8, hf.map_one] at e31
  rw [h4] at e32
  -- Compare each equation with its scaled version. The even step only needs the preceding
  -- even power; the odd step uses that even power and its successor.
  have hpairs (k : ℕ) : f (2 ^ (2 * k)) = (2 : ℂ) ^ (2 * (2 * k)) ∧
      f (2 ^ (2 * k + 1)) = (2 : ℂ) ^ (2 * (2 * k + 1)) := by
    induction k with
    | zero => norm_num [hf.map_one, h2]
    | succ k ih =>
      let d : ℕ := 2 ^ (2 * k)
      have hd : (2 ^ k : ℕ) ^ 2 = d := by rw [← pow_mul, Nat.mul_comm k]
      have hmul (i : ℕ) : d * 2 ^ i = 2 ^ (2 * k + i) := (pow_add _ _ _).symm
      have hcop {a : ℕ} (ha : Odd a) : d.Coprime a :=
        (Nat.coprime_two_left.mpr ha).pow_left _
      have he := scaled_parallelogram hpar (2 ^ k) 3 2 (by positivity) (by decide) (by decide)
      rw [hd] at he
      change f (d * 13) + f (d * 5) = 2 * f (d * 9) + 2 * f (d * 2 ^ 2) at he
      rw [hf.map_mul_of_coprime (hcop (by decide : Odd 13)),
        hf.map_mul_of_coprime (hcop (by decide : Odd 5)),
        hf.map_mul_of_coprime (hcop (by decide : Odd 9)), hmul] at he
      have ho := scaled_parallelogram hpar (2 ^ k) 3 1 (by positivity) (by decide) (by decide)
      rw [hd] at ho
      change f (d * (2 ^ 1 * 5)) + f (d * 2 ^ 3) = 2 * f (d * 9) + 2 * f (d * 1) at ho
      rw [← mul_assoc, hmul, hmul, hf.map_mul_of_coprime
        ((Nat.coprime_two_left.mpr (by decide : Odd 5)).pow_left _),
        hf.map_mul_of_coprime (hcop (by decide : Odd 9)), mul_one] at ho
      have hsucc : f (2 ^ (2 * k + 1)) = 4 * f d := by
        rw [ih.2, show f d = _ from ih.1, Nat.mul_add, pow_add]
        norm_num [mul_comm]
      rw [hsucc] at ho
      constructor
      · rw [show 2 * (k + 1) = 2 * k + 2 by omega,
          show 2 * (2 * k + 2) = 2 * (2 * k) + 4 by omega,
          pow_add (2 : ℂ) (2 * (2 * k)) 4, ← ih.1]
        change f (2 ^ (2 * k + 2)) = f d * (2 : ℂ) ^ 4
        linear_combination (f d * e32 - he) / 2
      · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
          show 2 * (2 * k + 3) = 2 * (2 * k) + 6 by omega,
          pow_add (2 : ℂ) (2 * (2 * k)) 6, ← ih.1]
        change f (2 ^ (2 * k + 3)) = f d * (2 : ℂ) ^ 6
        linear_combination ho - f d * e31
  intro r
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show r = 2 * k by omega]
    exact (hpairs k).1
  · rw [hk]
    exact (hpairs k).2

include hf hpar in
private theorem odd_prime_pow_values {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hind : ∀ q s : ℕ, q.Prime → q < p → 1 ≤ s → f (q ^ s) = (q : ℂ) ^ (2 * s))
    (hfp : f p = (p : ℂ) ^ 2) (r : ℕ) : f (p ^ r) = (p : ℂ) ^ (2 * r) := by
  have hplus := parallelogram_multiplicative_sq_add_one f hf hpar hp hind hp2 hfp
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hpge := hp.two_le
  have ht0 : 0 < t := by omega
  have hminusFactor : p ^ 2 - 1 = 4 * (t * (t + 1)) := by
    apply Nat.sub_eq_of_eq_add
    rw [ht]
    ring
  have hsmall (a : ℕ) (ha : 0 < a) (hap : a < p) (q : ℕ) (_ : q.Prime) (hd : q ∣ a) :
      q < p := (Nat.le_of_dvd ha hd).trans_lt hap
  have hminusSmooth : ∀ q : ℕ, q.Prime → q ∣ p ^ 2 - 1 → q < p := by
    rw [hminusFactor]
    intro q hq hd
    rcases hq.dvd_mul.mp hd with hq4 | hqt
    · have hq2 : q ∣ 2 := hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 from hq4)
      exact hsmall 2 (by decide) (by omega) q hq hq2
    · rcases hq.dvd_mul.mp hqt with hq0 | hq1
      · exact hsmall t ht0 (by omega) q hq hq0
      · exact hsmall (t + 1) (by omega) (by omega) q hq hq1
  have hminus := smooth_eq_sq f hf hind hminusSmooth
  have hcopMinus : p.Coprime (p ^ 2 - 1) :=
    hp.coprime_iff_not_dvd.mpr (fun hd => (hminusSmooth p hp hd).false)
  have hcopPlus : p.Coprime (p ^ 2 + 1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have h := (Nat.dvd_add_iff_right (dvd_pow_self p (by decide : 2 ≠ 0))).mpr hd
    exact hp.not_dvd_one h
  have hpow (k : ℕ) : (p ^ k : ℕ) ^ 2 = p ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k]
  have hevenStep (k : ℕ) : f (p ^ (2 * k + 2)) = f (p ^ (2 * k)) * (p : ℂ) ^ 4 := by
    have e := scaled_parallelogram hpar (p ^ k) p 1 (by positivity) (by decide) (by omega)
    rw [hpow, one_pow, mul_one,
      hf.map_mul_of_coprime (hcopPlus.pow_left _), hf.map_mul_of_coprime (hcopMinus.pow_left _),
      hplus, hminus, ← pow_add] at e
    have hp1 : 1 ≤ p ^ 2 := Nat.pow_pos hp.pos
    push_cast [Nat.cast_sub hp1] at e
    linear_combination -e / 2
  have heven (k : ℕ) : f (p ^ (2 * k)) = (p : ℂ) ^ (2 * (2 * k)) := by
    induction k with
    | zero => simp [hf.map_one]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, hevenStep, ih,
        show 2 * (2 * k + 2) = 2 * (2 * k) + 4 by omega, pow_add]
  rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show r = 2 * k by omega]
    exact heven k
  · -- Consecutive bases give a difference of `p`. The sum and the two squares are
    -- coprime to `p`, so comparing with the unscaled equation leaves only `f (p ^ r)`.
    have hdiff : (t + 1) ^ 2 - t ^ 2 = p := by
      apply Nat.sub_eq_of_eq_add
      rw [ht]
      ring
    have hsum : 2 * ((t + 1) ^ 2 + t ^ 2) = p ^ 2 + 1 := by rw [ht]; ring
    have hcopSum : p.Coprime ((t + 1) ^ 2 + t ^ 2) := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      exact (hp.coprime_iff_not_dvd.mp hcopPlus) (hsum ▸ dvd_mul_of_dvd_right hd 2)
    have hcopT : p.Coprime t := hp.coprime_iff_not_dvd.mpr
      (fun hd => (hsmall t ht0 (by omega) p hp hd).false)
    have hcopT' : p.Coprime (t + 1) := hp.coprime_iff_not_dvd.mpr
      (fun hd => (hsmall (t + 1) (by omega) (by omega) p hp hd).false)
    have e := hpar (t + 1) t ht0 (by omega)
    rw [hdiff] at e
    have es := scaled_parallelogram hpar (p ^ k) (t + 1) t (by positivity) ht0 (by omega)
    rw [hpow, hdiff, hf.map_mul_of_coprime (hcopSum.pow_left _),
      hf.map_mul_of_coprime (hcopT'.pow _ 2), hf.map_mul_of_coprime (hcopT.pow _ 2),
      show p ^ (2 * k) * p = p ^ (2 * k + 1) by rw [pow_add, pow_one]] at es
    have hstep : f (p ^ (2 * k + 1)) = f (p ^ (2 * k)) * f p := by
      linear_combination es - f (p ^ (2 * k)) * e
    rw [hk, hstep, heven, hfp, Nat.mul_add, pow_add]
    norm_num

set_option maxHeartbeats 1200000 in
-- The exact Table 1 certificates normalize products of polynomials of degree up to six.
include hf hpar in
private theorem small_values_of_four_ne_zero (h4 : f 4 ≠ 0) :
    f 2 = 4 ∧ f 3 = 9 ∧ f 4 = 16 ∧ f 7 = 49 ∧ f 8 = 64 ∧ f 11 = 121 := by
  -- Specialize the parallelogram law at small pairs and split off coprime factors.
  have h10 : f 10 = f 2 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 5)
  have h12 : f 12 = f 4 * f 3 := hf.map_mul_of_coprime (by decide : Nat.Coprime 4 3)
  have h15 : f 15 = f 3 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 3 5)
  have h20 : f 20 = f 4 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 4 5)
  have h24 : f 24 = f 8 * f 3 := hf.map_mul_of_coprime (by decide : Nat.Coprime 8 3)
  have h26 : f 26 = f 2 * f 13 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 13)
  have h33 : f 33 = f 3 * f 11 := hf.map_mul_of_coprime (by decide : Nat.Coprime 3 11)
  have h34 : f 34 = f 2 * f 17 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 17)
  have h35 : f 35 = f 5 * f 7 := hf.map_mul_of_coprime (by decide : Nat.Coprime 5 7)
  have h36 : f 36 = f 4 * f 9 := hf.map_mul_of_coprime (by decide : Nat.Coprime 4 9)
  have h40 : f 40 = f 8 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 8 5)
  have h48 : f 48 = f 16 * f 3 := hf.map_mul_of_coprime (by decide : Nat.Coprime 16 3)
  have h50 : f 50 = f 2 * f 25 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 25)
  have h63 : f 63 = f 9 * f 7 := hf.map_mul_of_coprime (by decide : Nat.Coprime 9 7)
  have h65 : f 65 = f 5 * f 13 := hf.map_mul_of_coprime (by decide : Nat.Coprime 5 13)
  have h72 : f 72 = f 8 * f 9 := hf.map_mul_of_coprime (by decide : Nat.Coprime 8 9)
  have h74 : f 74 = f 2 * f 37 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 37)
  have h77 : f 77 = f 7 * f 11 := hf.map_mul_of_coprime (by decide : Nat.Coprime 7 11)
  have h80 : f 80 = f 16 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 16 5)
  have h82 : f 82 = f 2 * f 41 := hf.map_mul_of_coprime (by decide : Nat.Coprime 2 41)
  have h85 : f 85 = f 5 * f 17 := hf.map_mul_of_coprime (by decide : Nat.Coprime 5 17)
  have h90 : f 90 = f 2 * f 9 * f 5 := by
    calc
      f 90 = f 18 * f 5 := hf.map_mul_of_coprime (by decide : Nat.Coprime 18 5)
      _ = f 2 * f 9 * f 5 := by rw [show f 18 = f 2 * f 9 from
        hf.map_mul_of_coprime (by decide : Nat.Coprime 2 9)]
  have h96 : f 96 = f 32 * f 3 := hf.map_mul_of_coprime (by decide : Nat.Coprime 32 3)
  have h100 : f 100 = f 4 * f 25 := hf.map_mul_of_coprime (by decide : Nat.Coprime 4 25)
  have h104 : f 104 = f 8 * f 13 := hf.map_mul_of_coprime (by decide : Nat.Coprime 8 13)
  have h130 : f 130 = f 2 * f 5 * f 13 := by
    calc
      f 130 = f 10 * f 13 := hf.map_mul_of_coprime (by decide : Nat.Coprime 10 13)
      _ = f 2 * f 5 * f 13 := by rw [show f 10 = f 2 * f 5 from
        hf.map_mul_of_coprime (by decide : Nat.Coprime 2 5)]
  have h136 : f 136 = f 8 * f 17 := hf.map_mul_of_coprime (by decide : Nat.Coprime 8 17)
  have e21 : f 5 + f 3 = 2 * f 4 + 2 * 1 := by
    have e : f 5 + f 3 = 2 * f 4 + 2 * f 1 := hpar 2 1 (by decide) (by decide)
    simpa only [hf.map_one] using e
  have e31 : f 2 * f 5 + f 8 = 2 * f 9 + 2 * 1 := by
    have e : f 10 + f 8 = 2 * f 9 + 2 * f 1 := hpar 3 1 (by decide) (by decide)
    simpa only [h10, hf.map_one] using e
  have e32 : f 13 + f 5 = 2 * f 9 + 2 * f 4 := hpar 3 2 (by decide) (by decide)
  have e41 : f 17 + f 3 * f 5 = 2 * f 16 + 2 * 1 := by
    have e : f 17 + f 15 = 2 * f 16 + 2 * f 1 := hpar 4 1 (by decide) (by decide)
    simpa only [h15, hf.map_one] using e
  have e42 : f 4 * f 5 + f 4 * f 3 = 2 * f 16 + 2 * f 4 := by
    have e : f 20 + f 12 = 2 * f 16 + 2 * f 4 := hpar 4 2 (by decide) (by decide)
    simpa only [h20, h12] using e
  have e43 : f 25 + f 7 = 2 * f 16 + 2 * f 9 := hpar 4 3 (by decide) (by decide)
  have e51 : f 2 * f 13 + f 8 * f 3 = 2 * f 25 + 2 * 1 := by
    have e : f 26 + f 24 = 2 * f 25 + 2 * f 1 := hpar 5 1 (by decide) (by decide)
    simpa only [h26, h24, hf.map_one] using e
  have e53 : f 2 * f 17 + f 16 = 2 * f 25 + 2 * f 9 := by
    have e : f 34 + f 16 = 2 * f 25 + 2 * f 9 := hpar 5 3 (by decide) (by decide)
    simpa only [h34] using e
  have e54 : f 41 + f 9 = 2 * f 25 + 2 * f 16 := hpar 5 4 (by decide) (by decide)
  have e61 : f 37 + f 5 * f 7 = 2 * (f 4 * f 9) + 2 * 1 := by
    have e : f 37 + f 35 = 2 * f 36 + 2 * f 1 := hpar 6 1 (by decide) (by decide)
    simpa only [h35, h36, hf.map_one] using e
  have e62 : f 8 * f 5 + f 32 = 2 * (f 4 * f 9) + 2 * f 4 := by
    have e : f 40 + f 32 = 2 * f 36 + 2 * f 4 := hpar 6 2 (by decide) (by decide)
    simpa only [h40, h36] using e
  have e71 : f 2 * f 25 + f 16 * f 3 = 2 * f 49 + 2 * 1 := by
    have e : f 50 + f 48 = 2 * f 49 + 2 * f 1 := hpar 7 1 (by decide) (by decide)
    simpa only [h50, h48, hf.map_one] using e
  have e74 : f 5 * f 13 + f 3 * f 11 = 2 * f 49 + 2 * f 16 := by
    have e : f 65 + f 33 = 2 * f 49 + 2 * f 16 := hpar 7 4 (by decide) (by decide)
    simpa only [h65, h33] using e
  have e75 : f 2 * f 37 + f 8 * f 3 = 2 * f 49 + 2 * f 25 := by
    have e : f 74 + f 24 = 2 * f 49 + 2 * f 25 := hpar 7 5 (by decide) (by decide)
    simpa only [h74, h24] using e
  have e76 : f 5 * f 17 + f 13 = 2 * f 49 + 2 * (f 4 * f 9) := by
    have e : f 85 + f 13 = 2 * f 49 + 2 * f 36 := hpar 7 6 (by decide) (by decide)
    simpa only [h85, h36] using e
  have e81 : f 5 * f 13 + f 9 * f 7 = 2 * f 64 + 2 * 1 := by
    have e : f 65 + f 63 = 2 * f 64 + 2 * f 1 := hpar 8 1 (by decide) (by decide)
    simpa only [h65, h63, hf.map_one] using e
  have e84 : f 16 * f 5 + f 16 * f 3 = 2 * f 64 + 2 * f 16 := by
    have e : f 80 + f 48 = 2 * f 64 + 2 * f 16 := hpar 8 4 (by decide) (by decide)
    simpa only [h80, h48] using e
  have e91 : f 2 * f 41 + f 16 * f 5 = 2 * f 81 + 2 * 1 := by
    have e : f 82 + f 80 = 2 * f 81 + 2 * f 1 := hpar 9 1 (by decide) (by decide)
    simpa only [h82, h80, hf.map_one] using e
  have e92 : f 5 * f 17 + f 7 * f 11 = 2 * f 81 + 2 * f 4 := by
    have e : f 85 + f 77 = 2 * f 81 + 2 * f 4 := hpar 9 2 (by decide) (by decide)
    simpa only [h85, h77] using e
  have e93 : f 2 * f 9 * f 5 + f 8 * f 9 = 2 * f 81 + 2 * f 9 := by
    have e : f 90 + f 72 = 2 * f 81 + 2 * f 9 := hpar 9 3 (by decide) (by decide)
    simpa only [h90, h72] using e
  have e97 : f 2 * f 5 * f 13 + f 32 = 2 * f 81 + 2 * f 49 := by
    have e : f 130 + f 32 = 2 * f 81 + 2 * f 49 := hpar 9 7 (by decide) (by decide)
    simpa only [h130] using e
  have e10_2 : f 8 * f 13 + f 32 * f 3 = 2 * (f 4 * f 25) + 2 * f 4 := by
    have e : f 104 + f 96 = 2 * f 100 + 2 * f 4 := hpar 10 2 (by decide) (by decide)
    simpa only [h104, h96, h100] using e
  have e10_6 : f 8 * f 17 + f 64 = 2 * (f 4 * f 25) + 2 * (f 4 * f 9) := by
    have e : f 136 + f 64 = 2 * f 100 + 2 * f 36 := hpar 10 6 (by decide) (by decide)
    simpa only [h136, h100, h36] using e
  -- Eliminate values that occur linearly, leaving only the five values at 2, 4, 5, 9 and 11.
  have v3 : f 3 = 2 * f 4 - f 5 + 2 := by
    linear_combination e21
  have v16 : f 16 = f 4 ^ 2 := by
    have e := e42
    rw [v3] at e
    linear_combination -e / 2
  have v64 : f 64 = f 4 ^ 3 := by
    have e := e84
    rw [v3, v16] at e
    linear_combination -e / 2
  have v8 : f 8 = -f 2 * f 5 + 2 * f 9 + 2 := by
    linear_combination e31
  have v81 : f 81 = f 9 ^ 2 := by
    have e := e93
    rw [v8] at e
    linear_combination -e / 2
  have v13 : f 13 = 2 * f 4 - f 5 + 2 * f 9 := by
    linear_combination e32
  have v17 : f 17 = 2 * f 4 ^ 2 - 2 * f 4 * f 5 + f 5 ^ 2 - 2 * f 5 + 2 := by
    have e := e41
    rw [v3, v16] at e
    linear_combination e
  have v32 : f 32 = f 2 * f 5 ^ 2 + 2 * f 4 * f 9 + 2 * f 4 - 2 * f 5 * f 9 - 2 * f 5 := by
    have e := e62
    rw [v8] at e
    linear_combination e
  have v49 : f 49 = f 2 * f 4 * f 5 + f 2 * f 5 * f 9 + f 4 * f 9 + f 4 - f 5 * f 9 - f 5 - f 9 ^
    2 := by
    have e := e97
    rw [v81, v13, v32] at e
    linear_combination -e / 2
  have v25 : f 25 = f 2 * f 4 ^ 2 - f 2 * f 4 * f 5 + f 2 * f 5 ^ 2/2 - f 2 * f 5 + f 2 + f 4 ^
    2/2 - f 9 := by
    have e := e53
    rw [v16, v17] at e
    linear_combination -e / 2
  have v7 : f 7 = -f 2 * f 4 ^ 2 + f 2 * f 4 * f 5 - f 2 * f 5 ^ 2/2 + f 2 * f 5 - f 2 + 3 * f 4
    ^ 2/2 + 3 * f 9 := by
    have e := e43
    rw [v16, v25] at e
    linear_combination e
  have v41 : f 41 = 2 * f 2 * f 4 ^ 2 - 2 * f 2 * f 4 * f 5 + f 2 * f 5 ^ 2 - 2 * f 2 * f 5 + 2 *
    f 2 + 3 * f 4 ^ 2 - 3 * f 9 := by
    have e := e54
    rw [v16, v25] at e
    linear_combination e
  have v37 : f 37 = f 2 * f 4 ^ 2 * f 5 - f 2 * f 4 * f 5 ^ 2 + f 2 * f 5 ^ 3/2 - f 2 * f 5 ^ 2 +
    f 2 * f 5 - 3 * f 4 ^ 2 * f 5/2 + 2 * f 4 * f 9 - 3 * f 5 * f 9 + 2 := by
    have e := e61
    rw [v7] at e
    linear_combination e
  rw [v3, v8, v13, v25] at e51
  rw [v3, v16, v49, v25] at e71
  rw [v3, v16, v13, v49] at e74
  rw [v3, v8, v49, v25, v37] at e75
  rw [v13, v17, v49] at e76
  rw [v64, v13, v7] at e81
  rw [v16, v81, v41] at e91
  rw [v81, v17, v7] at e92
  rw [v3, v8, v13, v32, v25] at e10_2
  rw [v64, v8, v17, v25] at e10_6
  -- This exact polynomial certificate fixes f(2) in every branch of the small system.
  have ha : f 2 - 4 = 0 := by
    -- Clear the denominators in the exact linear combination.
    have certificate : (1138159028425414179278660223386732463120599576 : ℂ) * (f 2 - 4) = 0 := by
      linear_combination
        (645013644260505797960096280248637370772817348 * f 11 * f 2 +
          5882952732869335765087929692374927076517605470 * f 11 * f 4 -
          933387349645796544116308648100147515018517759 * f 11 * f 5 +
          1616569820867129346862114213438649679303339200 * f 11 * f 9 -
          2293485086416513338357730935485589957436508750 * f 11 -
          1290027288521011595920192560497274741545634696 * f 2 ^ 2 * f 5 +
          645013644260505797960096280248637370772817348 * f 2 ^ 2 +
          13379281487359227148186867535439547903781642328 * f 2 * f 4 ^ 2 -
          2832461995085339481472733737819408302257248064 * f 2 * f 4 * f 5 +
          4666123256240472312143004848942819362231227052 * f 2 * f 4 * f 9 -
          4322858718828865302796667878710542486416848118 * f 2 * f 4 -
          31373386893782490639760328963942908596414674 * f 2 * f 5 ^ 2 -
          1340229958989506634103000643937373351810444786 * f 2 * f 5 * f 9 -
          5797057175139291241442065151068314431456726476 * f 2 * f 5 -
          15141943431963771458892411915696326403443216608 * f 2 * f 9 +
          12783804836085360797573302426089858618526008656 * f 2 +
          3505526855223098091909738709093719048650773774 * f 4 ^ 2 +
          346043898311785685967249113233200332396516578 * f 4 * f 5 -
          39160203585281832491873096950660457508074939462 * f 4 * f 9 -
          36186240972322585391389284639687067882971733950 * f 4 +
          3372961335201426976086269473164783883439565677 * f 5 ^ 2 +
          22394554283371853474415858455677229749653145540 * f 5 * f 9 +
          12963790440021478366429336440343106023263608650 * f 5 -
          2512947230501711234532946708794558927763759218 * f 9 ^ 2 -
          39492387021879200874246547385137858285046280340 * f 9 -
          26682447276733072729613606913774107888288000092) * e76
        + (2 * (822541563024528372905890315034427658745508699 * f 11 * f 2 * f 5 +
          322506822130252898980048140124318685386408674 * f 11 * f 2 +
          2989135006719694548404467498736499384724374992 * f 11 * f 4 ^ 2 -
          2584992551502912211688938945376836964898540192 * f 11 * f 4 * f 5 -
          5288601892999157781578404684430325939074673789 * f 11 * f 4 +
          1526734975956247506530901395665070886832215308 * f 11 * f 5 ^ 2 -
          1174070252612939876051092232655715106794831567 * f 11 * f 5 -
          836798215615492072380723523349530477839347798 * f 11 * f 9 -
          6382494346011483364694412027548790818758488557 * f 11 +
          1811408675754294273119482309029629804523338736 * f 2 ^ 2 * f 5 +
          469989890971595908949291336137657596513877980 * f 2 * f 4 ^ 2 -
          600640885641566208090981557909062340963138802 * f 2 * f 4 -
          19143440082919778214910228083890715657262288508 * f 2 * f 5 ^ 2 -
          5464301789074004262811786609923656593006963973 * f 2 * f 5 * f 9 +
          10319755614083710975067219433427202707072327466 * f 2 * f 5 -
          2649413302859384816176960960802375017941234132 * f 2 * f 9 -
          418893207652868643662028776258249623912234818 * f 2 +
          2148805991221481288712039344608769449540657802 * f 4 ^ 3 +
          4687167655473678608406291216531785787705744025 * f 4 ^ 2 * f 5 -
          1285667797178968030658932016235868083268888752 * f 4 ^ 2 * f 9 -
          893065530959003669796433496257719600237961628 * f 4 ^ 2 -
          6132233389821175834980127940136275238493168303 * f 4 * f 5 ^ 2 +
          3292126854940037079880340794000842574866733435 * f 4 * f 5 * f 9 +
          10228857933293267113908653903997027402409725277 * f 4 * f 5 -
          37274544173275168691119610784028595703942725402 * f 4 * f 9 -
          36735076150217705995076593913121224045604742017 * f 4 +
          4213762856987050258773762958017982635187898957 * f 5 ^ 3 -
          1517283390938286062239222016728048012434058600 * f 5 ^ 2 * f 9 -
          7524677516405934296251021658102060156118504030 * f 5 ^ 2 +
          41244813133906085544331075848629876422061661666 * f 5 * f 9 +
          51101827197877121696523213311461315074680093348 * f 5 +
          5729213513277693778506936296245153180020630734 * f 9 ^ 2 -
          23136628282086084004256702714852904045875976490 * f 9 -
          28591451731448263803229398487196362350860430176)) * e51
        + (1290027288521011595920192560497274741545634696 * f 2 ^ 2 * f 5 -
          645013644260505797960096280248637370772817348 * f 2 ^ 2 -
          4666123256240472312143004848942819362231227052 * f 2 * f 4 * f 9 +
          5743186601802475156456551461307104456939233686 * f 2 * f 4 +
          1447604384436452231376127197873647059725038706 * f 2 * f 5 ^ 2 +
          1340229958989506634103000643937373351810444786 * f 2 * f 5 * f 9 -
          20150191336256017859324774645656406097896370440 * f 2 * f 5 +
          11396355608194767320951428576573643946761395704 * f 2 * f 9 -
          4426122428056119913248342620156978091977749478 * f 2 +
          4939260085311833833974641215031146691993952150 * f 4 ^ 3 -
          11058639144568099178497325978542162490392767040 * f 4 ^ 2 * f 5 -
          368042796221274318117826495913404939134877192 * f 4 ^ 2 * f 9 -
          24099031985111695484086275828390647743098485356 * f 4 ^ 2 +
          5882952732869335765087929692374927076517605470 * f 4 * f 5 ^ 2 +
          368042796221274318117826495913404939134877192 * f 4 * f 5 * f 9 +
          5580696719038574558329457813462621410886280980 * f 4 * f 5 +
          14686483909637772844252580367520420822089518328 * f 4 * f 9 +
          25624110207956049394650641523786522418382817056 * f 4 -
          933387349645796544116308648100147515018517759 * f 5 ^ 3 -
          184021398110637159058913247956702469567438596 * f 5 ^ 2 * f 9 -
          6021304386557818284913723018114467907509374470 * f 5 ^ 2 -
          5933908824603663216694805320506191441922108634 * f 5 * f 9 -
          10405526243109663821300821226124846618293238453 * f 5 +
          1352840656899130512347036556175623170849152170 * f 9 ^ 2 +
          13254258537326217483739612325180186764177946938 * f 9 +
          7110454588046927923780223043432508180864844620) * e74
        + (4 * (-321268534570163938858311463606817118986758492 * f 11 * f 4 +
          310966525236779860368956248697370243886509386 * f 11 * f 5 +
          626791689471622117073987900543091011801497480 * f 11 +
          1839651451389428375221139879694362088333373532 * f 2 * f 4 -
          1002234392112883363917480534799072070376004033 * f 2 * f 5 +
          701568321157661711781507810622508431976478222 * f 2 * f 9 -
          1375170369187740159933743606757910554477286776 * f 2 +
          207458558044047457450436338530610723649092551 * f 4 ^ 2 -
          217245774375313219935095011582574551917839518 * f 4 * f 5 -
          1058776874442887813592140148001866623833876096 * f 4 * f 9 -
          1595618450569407626967347328880509143254818183 * f 4 +
          524283150509811440748372859274647224104643670 * f 5 ^ 2 +
          500260092085443363708686283989168830760048841 * f 5 * f 9 -
          3149165813843762403236644732630702911919009547 * f 5 +
          32167472596400232328667646296821194470027812 * f 9 ^ 2 -
          2348312518212470582369045059498385220222462978 * f 9 -
          3545887234576297024519311166785851273564608414)) * e91
        + (-4 * (77861826987680697093714737941074616167500018 * f 11 * f 2 +
          1303163480704325060052907829387304117937850947 * f 11 * f 4 -
          481807020290884610158741155308381450300521981 * f 11 * f 5 -
          32167472596400232328667646296821194470027812 * f 11 * f 9 +
          834211529629164566093739360938520916214775136 * f 11 +
          297171274810897458630271993379347422257686896 * f 2 ^ 2 -
          1918393314177812969373046462539600707512356964 * f 2 * f 4 -
          4177272213920784915013421963233207937795847122 * f 2 * f 5 -
          354361588593445645203812830748376328168707386 * f 2 * f 9 +
          3492306753151216477069390714265803379233449864 * f 2 -
          1547844339492433283922501997907108420923069624 * f 4 ^ 2 +
          1030754427250481518301076620849468699196943450 * f 4 * f 5 +
          92010699055318579529456623978351234783719298 * f 4 * f 9 +
          255148080082419589396594165960194243349365902 * f 4 -
          469436407933965817225058447357271698059688874 * f 5 ^ 2 -
          92010699055318579529456623978351234783719298 * f 5 * f 9 -
          1180443459088863362408697730928573421516312006 * f 5 +
          10590195826618639526860645931052400228196884290 * f 9 +
          9897478819766084533149147897009103458691282808)) * e81
        + (-2 * (322506822130252898980048140124318685386408674 * f 2 ^ 2 +
          4119177631756819666797729035275588330303174414 * f 2 * f 4 -
          3704580196697236854802178959048908390483575087 * f 2 * f 5 +
          652561256458203279243627630837175607316669564 * f 2 * f 9 -
          513883055291109742234497327102187350363562703 * f 2 +
          1056641253737002297147305647269669698159163820 * f 4 ^ 2 -
          2768454417278775039560340289570863372060544446 * f 4 * f 5 -
          2606326961408650120105815658774608235875701894 * f 4 * f 9 -
          9696519828992199007078196712712848353767054036 * f 4 +
          2153174342423611760101289060632465699229041718 * f 5 ^ 2 +
          963614040581769220317482310616762900601043962 * f 5 * f 9 +
          94775496553833683034126589514335390294901224 * f 5 +
          64334945192800464657335292593642388940055624 * f 9 ^ 2 -
          3532128748186274794136390055784575412778310076 * f 9 -
          7144706929705641788195620039181409013528708084)) * e92
        + (2 * (-698908482683234853059978227005191934556538580 * f 11 * f 2 -
          2864956835067975736546343228461326955470627882 * f 11 * f 4 +
          1044419698615405647721976884019411655144493047 * f 11 * f 5 -
          1392025994113273146518978353131606598939011926 * f 11 +
          1833422240996544794008798697588401085469199804 * f 2 ^ 2 -
          2478611553366278671760604756207076090185045878 * f 2 * f 4 +
          17139190836505417809713002530201189887334747798 * f 2 * f 5 -
          4161583834113463015936115246841482348235254578 * f 2 * f 9 -
          16061145767307997124509499435053607630340185820 * f 2 -
          2148805991221481288712039344608769449540657802 * f 4 ^ 2 +
          2029807964269110759062672728627879928386086127 * f 4 * f 5 -
          722087609152708542616986970777156128768431678 * f 4 * f 9 -
          7522077764932837836858493638739392443053455969 * f 4 -
          1584736722547274435468473736259205821104702319 * f 5 ^ 2 +
          1248039643626389825026547832380604795550516525 * f 5 * f 9 +
          10299673184667345165502874761409374002788731548 * f 5 +
          92010699055318579529456623978351234783719298 * f 9 ^ 2 +
          6929364615053522969499896943939054523111113683 * f 9 +
          70496319289363016849011260398767528737932676)) * e10_6
        + (-2 * (322506822130252898980048140124318685386408674 * f 11 * f 2 +
          2586837332793576871672659004789848405978200208 * f 11 * f 4 -
          461368783520147619187431851951904782275106648 * f 11 * f 5 +
          808284910433564673431057106719324839651669600 * f 11 * f 9 +
          703256414074367130141261714572901955296792521 * f 11 +
          68943972056035366627997505541386573348417048 * f 2 * f 4 -
          11298599401953211589926484152432350061489093212 * f 2 * f 5 +
          3400615834252441764386575229248728572421286680 * f 2 * f 9 -
          5500681476750960639734974427031642217909147104 * f 2 -
          6639721717251524129188344275634174912613444224 * f 4 ^ 2 +
          6549076974356468735480244530688144744341960520 * f 4 * f 5 +
          633057627973869697667016398823470370599824526 * f 4 * f 9 +
          14259521579742487433428843488391685271651120152 * f 4 -
          3060245190191168960779209457079582884383994970 * f 5 ^ 2 +
          324226737203542848583079008832122724140309316 * f 5 * f 9 -
          3612181544107190402456471018131652553213333048 * f 5 -
          580053286801290361092955076309467878457303524 * f 9 ^ 2 +
          20027081673504925356033173079862898705332591504 * f 9 -
          4823388459769681800196904350755911815526417220)) * e71
        + (2 * (822541563024528372905890315034427658745508699 * f 11 * f 2 +
          404142455216782336715528553359662419825834800 * f 11 * f 4 +
          32167472596400232328667646296821194470027812 * f 11 * f 5 -
          456449131057630502874207560291980242751835637 * f 11 +
          1811408675754294273119482309029629804523338736 * f 2 ^ 2 +
          5743399637108539742306358234947727397276075112 * f 2 * f 4 -
          19378435028405576169384873751959544455519227498 * f 2 * f 5 -
          190892042937060429454719711113586792244766841 * f 2 * f 9 +
          12001135425810024335607879022085086209398726918 * f 2 -
          2496964918719092710362850784955465110197985063 * f 4 * f 5 +
          459911066839243289353416989105915791114250806 * f 4 * f 9 +
          5833830026106617069013446347942976906664606586 * f 4 +
          1569050029100383190148593571777234366806494982 * f 5 ^ 2 -
          1454203681409312415186797953606415654496910033 * f 5 * f 9 -
          12862136595644647115734961363072194626277443027 * f 5 +
          23415903873509087284743693968120362139477165292 * f 9 +
          26432235092137833594979896985959759484417980713)) * e10_2
        + (2 * (2246611472912556833830746288365994081040371133 * f 11 +
          12301609850627266518441122828802444732083665724 * f 4 -
          8345838887509719847196250777197606175625894354 * f 5 +
          805241037687631814466241621251133297989013422 * f 9 +
          2624478207764521137556350983089048590639300012)) * e75
    exact (mul_eq_zero.mp certificate).resolve_left (by norm_num)
  have hf2 : f 2 = 4 := sub_eq_zero.mp ha
  simp only [hf2] at e51 e71 e74 e75 e76 e81 e91 e92 e10_2 e10_6
  -- Now the remaining branches are separated by f(4) * (f(4) - 16) = 0.
  have hc : f 4 * (f 4 - 16) = 0 := by
    -- Clear the denominators in the exact linear combination.
    have certificate : (7987214677786 : ℂ) * (f 4 * (f 4 - 16)) = 0 := by
      linear_combination
        (1443984973520 * f 4 ^ 2 - 783021241328 * f 4 * f 5 + 1849800612856 * f 4 + 369104002541
          * f 5 ^ 2 + 4348395080970 * f 5 + 28313016364 * f 9 + 409597351267) * e51
        + (-2 * (2670312695949 * f 4 - 1950353487195 * f 5 + 724111026581 * f 9 + 6459188883667))
          * e91
        + (-2 * (2301272435928 * f 4 + 1073747642252 * f 5 - 1002825732313 * f 9 +
          6686569564299)) * e76
        + (4 * (195755310332 * f 4 - 1386249689965 * f 5 - 5104188887872)) * e81
        + (7280953622168 * f 4 - 1031850511857 * f 5 - 1909193395380 * f 9 + 26516591255739) *
          e71
        + (575318108982 * f 4 + 268436910563 * f 5 - 1544680122408 * f 9 - 5514217888925) * e75
    exact (mul_eq_zero.mp certificate).resolve_left (by norm_num)
  have hf4 : f 4 = 16 := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left h4)
  simp only [hf4] at e51 e71 e74 e75 e76 e81 e91 e92 e10_2 e10_6
  have hf5 : f 5 = 25 := by
    clear * - f e51 e76 e81 e91
    grobner
  have hf9 : f 9 = 81 := by
    clear * - f e51 e76 e81 e91 hf5
    grobner
  have hf3 : f 3 = 9 := by norm_num [hf4, hf5] at v3 ⊢; exact v3
  have hf7 : f 7 = 49 := by norm_num [hf2, hf4, hf5, hf9] at v7 ⊢; exact v7
  have hf8 : f 8 = 64 := by norm_num [hf2, hf5, hf9] at v8 ⊢; exact v8
  have hf11 : f 11 = 121 := by
    clear * - f e92 hf5 hf9
    grobner
  exact ⟨hf2, hf3, hf4, hf7, hf8, hf11⟩

end

/-- **Parallelogram uniqueness of squares for multiplicative functions.** Let $f$ be a
complex-valued multiplicative arithmetic function
(so $f(0) = 0$) such that $f(m^2 + n^2) + f(m^2 - n^2) = 2f(m^2) + 2f(n^2)$ for all integers
$m > n \ge 1$, and suppose $f(4) \ne 0$. Then $f(n) = n^2$ for every natural number $n$.

Source: Poo-Sung Park, *On the Parallelogram Uniqueness of Square Numbers for Multiplicative
Functions*, INTEGERS 24 (2024), Article A108, Theorem 1 (`integers-2024-A108-thm-1`). -/
public theorem multiplicative_parallelogram_squares_eq_sq (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative)
    (hpar : ∀ m n : ℕ, 0 < n → n < m →
      f (m ^ 2 + n ^ 2) + f (m ^ 2 - n ^ 2) = 2 * f (m ^ 2) + 2 * f (n ^ 2))
    (h4 : f 4 ≠ 0) :
    ∀ n : ℕ, f n = (n : ℂ) ^ 2 := by
  obtain ⟨hf2, hf3, hf4, hf7, hf8, hf11⟩ := small_values_of_four_ne_zero hf hpar h4
  have hprime (p : ℕ) : p.Prime → ∀ r : ℕ, 1 ≤ r → f (p ^ r) = (p : ℂ) ^ (2 * r) := by
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      intro hp r _
      by_cases hp2 : p = 2
      · subst p
        simpa only [Nat.cast_ofNat] using two_pow_values hf hpar hf2 hf4 hf8 r
      have hind (q s : ℕ) (hq : q.Prime) (hqp : q < p) (hs : 1 ≤ s) := ih q hqp hq s hs
      have hfp : f p = (p : ℂ) ^ 2 := by
        by_cases hp4 : p % 4 = 1
        · exact parallelogram_multiplicative_prime_one_mod_four f hf hpar hp hind hp4
        obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
        by_cases h19 : 19 ≤ p
        · exact parallelogram_multiplicative_prime_three_mod_four f hf hpar hp hind
            (k := p / 4 + 1) (by omega) h19
        have hp_cases : p = 3 ∨ p = 7 ∨ p = 11 ∨ p = 15 := by omega
        rcases hp_cases with rfl | rfl | rfl | rfl
        · norm_num [hf3]
        · norm_num [hf7]
        · norm_num [hf11]
        · exact (by decide : ¬Nat.Prime 15) hp |>.elim
      exact odd_prime_pow_values hf hpar hp hp2 hind hfp r
  intro n
  by_cases hn : n = 0
  · simp [hn]
  apply smooth_eq_sq f hf (p := n + 1)
    (fun q s hq _ hs => hprime q hq s hs)
  intro q _ hqd
  exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hqd)

end MetaMathlibExt
