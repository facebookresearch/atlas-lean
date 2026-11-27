/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cubes with neighbors of prime-cube-times-square form

We prove that the two neighbors of a positive cube cannot both be products
of a prime cube and a positive square.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

namespace not_exists_prime_cube_square_neighbors_of_cube

/-- In a coprime product of the indicated form, a nonsquare factor forces
the entire prime contribution into that factor. -/
private theorem isSquare_of_coprime_mul {a b p y : ℤ} (hp : Prime p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : IsCoprime a b)
    (h : a * b = p ^ 3 * y ^ 2) (hnsq : ¬ IsSquare b) : IsSquare a := by
  have square_of_dvd_right {u v : ℤ} (hu : 0 ≤ u) (huv : IsCoprime u v)
      (he : u * v = p ^ 3 * y ^ 2) (hd : p ∣ v) : IsSquare u := by
    obtain ⟨w, rfl⟩ := hd
    have hs : u * w = (p * y) ^ 2 := by
      apply mul_left_cancel₀ hp.ne_zero
      linear_combination he
    obtain ⟨t, ht | ht⟩ := Int.sq_of_isCoprime
      (huv.of_isCoprime_of_dvd_right (dvd_mul_left w p)) hs
    · exact (isSquare_iff_exists_sq u).mpr ⟨t, ht⟩
    · have hs0 : t ^ 2 = 0 := by linarith [sq_nonneg t]
      exact (isSquare_iff_exists_sq u).mpr ⟨t, by rw [ht, hs0, neg_zero]⟩
  have hd : p ∣ a * b := by
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_pow_self p (by decide)) _
  rcases hp.dvd_mul.mp hd with hpa | hpb
  · exact (hnsq (square_of_dvd_right hb hc.symm (by rwa [mul_comm b a]) hpa)).elim
  · exact square_of_dvd_right ha hc h hpb

private theorem coprime_three {a : ℤ} (ha : a % 3 ≠ 0) : IsCoprime a 3 := by
  rcases (show a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h
  · exact ⟨1, -(a / 3), by omega⟩
  · exact ⟨-1, a / 3 + 1, by omega⟩

private theorem square_mod_three_ne_two (a : ℤ) : a ^ 2 % 3 ≠ 2 := by
  rw [pow_two, Int.mul_emod]
  rcases (show a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 by omega) with h | h | h <;>
    norm_num [h]

private theorem quadratic_pos (a : ℤ) : 0 < a ^ 2 + a + 1 := by
  nlinarith [sq_nonneg (2 * a + 1)]

private theorem quadratic_not_square {a : ℤ} (ha : 0 < a ∨ a < -1) :
    ¬ IsSquare (a ^ 2 + a + 1) := by
  suffices h : ∀ n : ℤ, 0 < n → ¬ IsSquare (n ^ 2 + n + 1) by
    rcases ha with ha | ha
    · exact h a ha
    · convert h (-a - 1) (by omega) using 2
      ring
  rintro n hn ⟨b, hb⟩
  have hlo : n ^ 2 < |b| ^ 2 := by rw [sq_abs]; nlinarith
  have hhi : |b| ^ 2 < (n + 1) ^ 2 := by rw [sq_abs]; nlinarith
  have hl := (sq_lt_sq₀ hn.le (abs_nonneg b)).mp hlo
  have hh := (sq_lt_sq₀ (abs_nonneg b) (by omega)).mp hhi
  omega

/-- If the product were a square, twice its nonnegative root would be
strictly between the sum of the factors minus one and the sum itself. -/
private theorem close_factors_not_square {a : ℤ} (ha : a ≠ 1) :
    ¬ IsSquare ((a ^ 2 + 2) * (a ^ 2 + a + 1)) := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨b, hb⟩
  have hsum : 0 ≤ a ^ 2 + 2 + (a ^ 2 + a + 1) - 1 := by
    linarith [quadratic_pos a, sq_nonneg a]
  have hroot : (2 * |b|) ^ 2 = 4 * ((a ^ 2 + 2) * (a ^ 2 + a + 1)) := by
    rw [mul_pow, sq_abs, ← hb]
    norm_num
  have hlo : (a ^ 2 + 2 + (a ^ 2 + a + 1) - 1) ^ 2 < (2 * |b|) ^ 2 := by
    rw [hroot]
    nlinarith [sq_nonneg (a + 2), sq_nonneg a]
  have hhi : (2 * |b|) ^ 2 < (a ^ 2 + 2 + (a ^ 2 + a + 1)) ^ 2 := by
    rw [hroot]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr ha)]
  have hnonneg : 0 ≤ 2 * |b| := by positivity
  have hl := (sq_lt_sq₀ hsum hnonneg).mp hlo
  have hh := (sq_lt_sq₀ hnonneg (by omega)).mp hhi
  omega

end not_exists_prime_cube_square_neighbors_of_cube

open not_exists_prime_cube_square_neighbors_of_cube

/-- **No cube whose neighbours are prime cubes times squares.** There are no primes $p$, $q$
and positive integers $x$, $y$, $z$ with $x^3 - 1 = p^3 y^2$ and $x^3 + 1 = q^3 z^2$.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Theorem 1. -/
public theorem not_exists_prime_cube_square_neighbors_of_cube :
    ¬ ∃ p q x y z : ℕ,
      p.Prime ∧ q.Prime ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
        (x : ℤ) ^ 3 - 1 = (p : ℤ) ^ 3 * (y : ℤ) ^ 2 ∧
          (x : ℤ) ^ 3 + 1 = (q : ℤ) ^ 3 * (z : ℤ) ^ 2 := by
  rintro ⟨p, q, x, y, z, hp, hq, hx, hy, _, hminus, hplus⟩
  set n : ℤ := (x : ℤ)
  have hp' := Nat.prime_iff_prime_int.mp hp
  have hq' := Nat.prime_iff_prime_int.mp hq
  have hn : 2 < n := by
    have hp3 : 8 ≤ (p : ℤ) ^ 3 :=
      pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) (by exact_mod_cast hp.two_le) 3
    have hy2 : 1 ≤ (y : ℤ) ^ 2 := one_le_pow₀ (by exact_mod_cast hy)
    have hprod : 8 ≤ (p : ℤ) ^ 3 * (y : ℤ) ^ 2 := by
      simpa using (mul_le_mul hp3 hy2 (by decide : (0 : ℤ) ≤ 1) (by omega))
    by_contra! hn
    have hn3 : n ^ 3 ≤ 8 := pow_le_pow_left₀ (by positivity) hn 3
    linarith
  -- The two residue classes 0 and 1 would force a square congruent to 2 modulo 3.
  by_cases hn1 : n % 3 = 1
  · have hc : IsCoprime (n + 1) (n ^ 2 - n + 1) := by
      rw [show n ^ 2 - n + 1 = 3 + (n + 1) * (n - 2) by ring, IsCoprime.add_mul_left_right_iff]
      exact coprime_three (by omega)
    have hnsq : ¬ IsSquare (n ^ 2 - n + 1) := by
      rw [show n ^ 2 - n + 1 = (n - 1) ^ 2 + (n - 1) + 1 by ring]
      exact quadratic_not_square (Or.inl (by omega))
    have hsq := isSquare_of_coprime_mul (y := (z : ℤ))
      hq' (by omega) (by nlinarith [sq_nonneg (2 * n - 1)])
      hc (by linear_combination hplus) hnsq
    obtain ⟨a, ha⟩ := (isSquare_iff_exists_sq _).mp hsq
    have hmod := square_mod_three_ne_two a
    rw [← ha] at hmod
    omega
  have hc : IsCoprime (n - 1) (n ^ 2 + n + 1) := by
    rw [show n ^ 2 + n + 1 = 3 + (n - 1) * (n + 2) by ring, IsCoprime.add_mul_left_right_iff]
    exact coprime_three (by omega)
  have hsq := isSquare_of_coprime_mul (y := (y : ℤ)) hp' (by omega) (quadratic_pos n).le hc
    (by linear_combination hminus) (quadratic_not_square (Or.inl (by omega)))
  obtain ⟨b, hb⟩ := (isSquare_iff_exists_sq _).mp hsq
  have hn2 : n % 3 = 2 := by
    have hmod := square_mod_three_ne_two b
    rw [← hb] at hmod
    omega
  obtain ⟨a, ha, ha1⟩ : ∃ a : ℤ, n - 1 = a ^ 2 ∧ a % 3 = 1 := by
    rcases (show b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 by omega) with h | h | h
    · have hmod : b ^ 2 % 3 = 1 := by rw [← hb]; omega
      norm_num [pow_two, Int.mul_emod, h] at hmod
    · exact ⟨b, hb, h⟩
    · exact ⟨-b, by simpa using hb, by omega⟩
  have halarge : 1 < a ∨ a < -1 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ a + 1 by omega) (show 0 ≤ 1 - a by omega)]
  -- With n = a² + 1, split n² - n + 1 into two quadratic factors.
  have hs : IsCoprime (a ^ 2 - a + 1) (a ^ 2 + 2) := by
    rw [show a ^ 2 + 2 = a + 1 + (a ^ 2 - a + 1) * 1 by ring,
      IsCoprime.add_mul_left_right_iff, isCoprime_comm,
      show a ^ 2 - a + 1 = 3 + (a + 1) * (a - 2) by ring, IsCoprime.add_mul_left_right_iff]
    exact coprime_three (by omega)
  have hs' : IsCoprime (a ^ 2 - a + 1) (a ^ 2 + a + 1) := by
    have hodd : Odd (a ^ 2 - a + 1) := by
      simpa only [mul_sub, mul_one, ← pow_two] using (Int.even_mul_pred_self a).add_one
    have hca : IsCoprime (a ^ 2 - a + 1) a := ⟨1, 1 - a, by ring⟩
    rw [show a ^ 2 + a + 1 = 2 * a + (a ^ 2 - a + 1) * 1 by ring,
      IsCoprime.add_mul_left_right_iff]
    exact hodd.isCoprime_two.mul_right hca
  have hfac : ((a ^ 2 + 2) * (a ^ 2 + a + 1)) * (a ^ 2 - a + 1) =
      (q : ℤ) ^ 3 * (z : ℤ) ^ 2 := by
    rw [show (q : ℤ) ^ 3 * (z : ℤ) ^ 2 = (a ^ 2 + 1) ^ 3 + 1 by
      rw [← hplus, show n = a ^ 2 + 1 by linarith]]
    ring
  have hspos : 0 < a ^ 2 - a + 1 := by nlinarith [quadratic_pos (-a)]
  have hnsq : ¬ IsSquare (a ^ 2 - a + 1) := by
    rw [show a ^ 2 - a + 1 = (-a) ^ 2 + (-a) + 1 by ring]
    exact quadratic_not_square (by omega)
  have hsq := isSquare_of_coprime_mul hq' (mul_nonneg (by positivity) (quadratic_pos a).le)
    hspos.le (hs.mul_right hs').symm hfac hnsq
  exact close_factors_not_square (by omega) hsq

end MathlibExt.NumberTheory.PowerfulNumbersWanted
