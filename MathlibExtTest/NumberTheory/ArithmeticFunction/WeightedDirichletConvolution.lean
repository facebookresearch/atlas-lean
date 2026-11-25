/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.WeightedDirichletConvolution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.NormNum

open ArithmeticFunction Finset MetaMathlibExt
open scoped ArithmeticFunction.Moebius

-- Below the first positive integer, the expansion vanishes for every choice of weights.
example (w u v : ArithmeticFunction ℂ) {x : ℝ} (hx : x < 1) :
    (∑ r ∈ Icc 1 ⌊x⌋₊, (w * (μ : ArithmeticFunction ℂ)) r *
      ∑ j ∈ Icc 1 ⌊x / r⌋₊, (u * v) (r * j)) = 0 := by
  rw [← sum_mul_dirichletConvolution_eq_sum_moebius]
  simp [Nat.floor_eq_zero.mpr hx]

-- At 5/2 the divisor 1 contributes both terms, while the divisor 2 contributes only the second.
example (w u v : ArithmeticFunction ℂ) :
    w 1 * (u * v) 1 + w 2 * (u * v) 2 =
      (w * (μ : ArithmeticFunction ℂ)) 1 * ((u * v) 1 + (u * v) 2) +
      (w * (μ : ArithmeticFunction ℂ)) 2 * (u * v) 2 := by
  have h := sum_mul_dirichletConvolution_eq_sum_moebius w u v (5 / 2)
  have hfloor : ⌊(5 : ℝ) / 2⌋₊ = 2 := Nat.floor_div_eq_div 5 2
  have hIcc : Icc 1 2 = {1, 2} := by decide
  simpa [Nat.floor_div_natCast, hfloor, hIcc] using h

open scoped ArithmeticFunction.zeta

local notation "Z" => (↑ζ : ArithmeticFunction ℂ)

private theorem complexZeta_completelyMultiplicative : IsCompletelyMultiplicative Z := by
  intro m n
  simp [ArithmeticFunction.natCoe_apply, zeta_apply]
  split_ifs <;> simp_all

private theorem complexZeta_convolution_two_pow (k : ℕ) :
    (Z * Z) (2 ^ k) = (k : ℂ) + 1 := by
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [ArithmeticFunction.natCoe_apply, zeta_apply_ne (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))]

-- The divisors 1 and 2 contribute 3 * 4 and -2 * 3; the 4 term vanishes.
example : (Z * Z) (4 * 8) = 6 ∧
    (∑ m ∈ (Nat.gcd 4 8).divisors,
      (μ m : ℂ) * Z m * Z m * (Z * Z) (4 / m) * (Z * Z) (8 / m)) = 6 := by
  constructor
  · change (Z * Z) (2 ^ 5) = 6
    rw [complexZeta_convolution_two_pow]
    norm_num
  · have hd : (Nat.gcd 4 8).divisors = {1, 2, 4} := by decide
    have h₂ : (Z * Z) 2 = 2 := by
      change (Z * Z) (2 ^ 1) = 2
      rw [complexZeta_convolution_two_pow]
      norm_num
    have h₄ : (Z * Z) 4 = 3 := by
      change (Z * Z) (2 ^ 2) = 3
      rw [complexZeta_convolution_two_pow]
      norm_num
    have h₈ : (Z * Z) 8 = 4 := by
      change (Z * Z) (2 ^ 3) = 4
      rw [complexZeta_convolution_two_pow]
      norm_num
    have hμ₄ : μ 4 = 0 := by
      change μ (2 ^ 2) = 0
      rw [moebius_apply_prime_pow Nat.prime_two (by decide), ite_eq_right (by decide)]
    rw [hd, Finset.sum_insert (by decide : 1 ∉ ({2, 4} : Finset ℕ)),
      Finset.sum_insert (by decide : 2 ∉ ({4} : Finset ℕ)), Finset.sum_singleton]
    change (μ 1 : ℂ) * Z 1 * Z 1 * (Z * Z) 4 * (Z * Z) 8 +
      ((μ 2 : ℂ) * Z 2 * Z 2 * (Z * Z) 2 * (Z * Z) 4 +
        (μ 4 : ℂ) * Z 4 * Z 4 * (Z * Z) 1 * (Z * Z) 2) = 6
    rw [h₂, h₄, h₈, moebius_apply_one, moebius_apply_prime Nat.prime_two, hμ₄]
    norm_num [ArithmeticFunction.natCoe_apply, zeta_apply]

-- Zero is completely multiplicative without being normalized at 1.
example :
    (∑ m ∈ (Nat.gcd 4 8).divisors,
      (μ m : ℂ) * (0 : ArithmeticFunction ℂ) m * Z m *
        (0 * Z) (4 / m) * (0 * Z) (8 / m)) = 0 := by
  have hz : (0 : ArithmeticFunction ℂ).IsCompletelyMultiplicative := by
    intro m n
    simp
  rw [← dirichletConvolution_mul_eq_sum_gcd
    (hu := hz) (hv := complexZeta_completelyMultiplicative) 4 8]
  simp

-- The divisor sum also vanishes when a convolution argument is zero.
example {u v : ArithmeticFunction ℂ} (hu : u.IsCompletelyMultiplicative)
    (hv : v.IsCompletelyMultiplicative) (s : ℕ) :
    (∑ m ∈ (Nat.gcd 0 s).divisors,
      (μ m : ℂ) * u m * v m * (u * v) (0 / m) * (u * v) (s / m)) = 0 := by
  rw [← dirichletConvolution_mul_eq_sum_gcd (hu := hu) (hv := hv)]
  simp
