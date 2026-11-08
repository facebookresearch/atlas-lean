/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.UnitaryConvolution

open ArithmeticFunction MetaMathlibExt

example : Nat.unitaryDivisors 12 = {1, 3, 4, 12} := by decide

example : Nat.unitaryDivisors (2 ^ 3) = {1, 2 ^ 3} :=
  Nat.unitaryDivisors_prime_pow Nat.prime_two 3

example : powOmega (2 : ℤ) 12 = 8 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num, (isCompletelyMultiplicative_powOmega _).map_mul,
    powOmega_prime_pow _ Nat.prime_two, powOmega_prime_pow _ Nat.prime_three]
  norm_num

example : powOmega (5 : ℤ) 0 = 0 := by decide

example : unitaryConv (powOmega (2 : ℤ)) (powOmega 3) 12 = 65 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num,
    (isMultiplicative_unitaryConv (isMultiplicative_powOmega _)
      (isMultiplicative_powOmega _)).map_mul_of_coprime (by norm_num),
    unitaryConv_prime_pow _ _ Nat.prime_two (by norm_num),
    unitaryConv_prime_pow _ _ Nat.prime_three (by norm_num),
    powOmega_prime_pow _ Nat.prime_two, powOmega_prime_pow _ Nat.prime_two,
    powOmega_prime_pow _ Nat.prime_three, powOmega_prime_pow _ Nat.prime_three]
  norm_num

example : multiplicativeOfPrimePowers (fun m => (m : ℤ) + 10) 12 = 132 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num,
    (isMultiplicative_multiplicativeOfPrimePowers _).map_mul_of_coprime (by norm_num),
    multiplicativeOfPrimePowers_prime_pow _ Nat.prime_two (by norm_num),
    multiplicativeOfPrimePowers_prime_pow _ Nat.prime_three (by norm_num)]
  norm_num

example : multiplicativeOfPrimePowers (fun m => (m : ℤ) + 10) 0 = 0 := by decide

example {R : Type*} [CommSemiring R] (c : R) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    powOmega c (p ^ m) = c ^ m :=
  powOmega_prime_pow c hp m

example {R : Type*} [CommSemiring R] (c : R) (m n : ℕ) :
    powOmega c (m * n) = powOmega c m * powOmega c n :=
  (isCompletelyMultiplicative_powOmega c).map_mul m n

example {R : Type*} [CommSemiring R] (f g : ArithmeticFunction R) {p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    unitaryConv f g (p ^ m) = f 1 * g (p ^ m) + f (p ^ m) * g 1 :=
  unitaryConv_prime_pow f g hp hm

example {R : Type*} [CommSemiring R] (a b : R) :
    (unitaryConv (powOmega a) (powOmega b)).IsMultiplicative :=
  isMultiplicative_unitaryConv (isMultiplicative_powOmega a) (isMultiplicative_powOmega b)

-- The unitary convolution of `a ^ Ω` and `b ^ Ω` is the multiplicative function with value
-- `a ^ m + b ^ m` at `p ^ m`, `m ≥ 1`.
example {R : Type*} [CommSemiring R] (a b : R) :
    unitaryConv (powOmega a) (powOmega b) =
      multiplicativeOfPrimePowers fun m => a ^ m + b ^ m := by
  refine eq_multiplicativeOfPrimePowers
    (isMultiplicative_unitaryConv (isMultiplicative_powOmega a) (isMultiplicative_powOmega b))
    _ fun p m hp hm => ?_
  rw [unitaryConv_prime_pow _ _ hp hm, powOmega_prime_pow _ hp, powOmega_prime_pow _ hp]
  simp [add_comm]

example {R : Type*} [CommMonoidWithZero R] (g : ℕ → R) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    multiplicativeOfPrimePowers g (p ^ m) = g m :=
  multiplicativeOfPrimePowers_prime_pow g hp hm

example {R : Type*} [CommMonoidWithZero R] (g : ℕ → R) {m n : ℕ} (h : m.Coprime n) :
    multiplicativeOfPrimePowers g (m * n) =
      multiplicativeOfPrimePowers g m * multiplicativeOfPrimePowers g n :=
  (isMultiplicative_multiplicativeOfPrimePowers g).map_mul_of_coprime h
