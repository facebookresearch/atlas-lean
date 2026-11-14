/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.SumPrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Tests for sums of primitive roots of unity
-/

@[expose] public section

open Finset Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

-- The primitive square roots of unity in `ℚ` are `{-1}`, summing to `μ 2 = -1`.
example : ∑ x ∈ primitiveRoots 2 ℚ, x = -1 := by
  rw [IsPrimitiveRoot.sum_primitiveRoots (IsPrimitiveRoot.neg_one 0 (by norm_num)) two_pos,
    moebius_apply_prime Nat.prime_two]
  norm_num

-- `n = 1`: the only primitive first root of unity is `1 = μ 1`.
example : ∑ x ∈ primitiveRoots 1 ℚ, x = 1 := by
  rw [IsPrimitiveRoot.sum_primitiveRoots IsPrimitiveRoot.one one_pos]
  simp

-- Primitive fourth roots of unity in `ℂ` sum to `μ 4 = 0`.
example : ∑ x ∈ primitiveRoots 4 ℂ, x = 0 := by
  rw [IsPrimitiveRoot.sum_primitiveRoots (Complex.isPrimitiveRoot_exp 4 (by norm_num))
    (by norm_num)]
  have : μ 4 = 0 := by decide +kernel
  simp [this]

example : ∑ x ∈ nthRootsFinset 3 (1 : ℂ), x = 0 :=
  IsPrimitiveRoot.sum_nthRootsFinset_one (Complex.isPrimitiveRoot_exp 3 (by norm_num))
    (by norm_num)

example : ∑ d ∈ (6 : ℕ).divisors, ∑ x ∈ primitiveRoots d ℂ, x = 0 := by
  rw [IsPrimitiveRoot.sum_divisors_sum_primitiveRoots
    (Complex.isPrimitiveRoot_exp 6 (by norm_num)) (by norm_num)]
  simp

/-! ### The subleading cyclotomic coefficient -/

-- `Φ₁ = X - 1`: the coefficient of `X⁰` is `-1 = -μ 1`, matching Mathlib's `cyclotomic_one`.
example : (cyclotomic 1 ℤ).coeff (Nat.totient 1 - 1) = -μ 1 :=
  cyclotomic_coeff_totient_sub_one ℤ one_pos
example : (cyclotomic 1 ℤ).coeff 0 = -1 := by simp [cyclotomic_one]

-- `Φ₄ = X² + 1`: the coefficient of `X¹` is `0 = -μ 4`.
example : (cyclotomic 4 ℤ).coeff 1 = 0 := by
  have h := cyclotomic_coeff_totient_sub_one ℤ (n := 4) (by norm_num)
  rw [show Nat.totient 4 - 1 = 1 by decide, show μ 4 = 0 by decide +kernel] at h
  simpa using h
