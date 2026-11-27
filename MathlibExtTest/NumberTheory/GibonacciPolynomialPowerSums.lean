/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GibonacciPolynomialPowerSums
import Mathlib.Tactic.NormNum

open MetaMathlibExt Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

-- At x = 1 the three surviving Fibonacci numbers are 1, 2, and 5.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔣 (2 * n + 1)) -
    1 / aeval (1 : ℝ) (𝔣 (2 * n + 1 + 6))) = 17 / 10 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_odd (x := 1) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 3) (by decide) (lam := 1) (by decide)
  have hIcc : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  simp only [pow_one] at h
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial])

-- With the smallest shift, only the first Lucas polynomial survives, even for 0 < x < 1.
example : ∑' n : ℕ, (1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1)) ^ 2 -
    1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1 + 2)) ^ 2) = 4 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_odd (x := 1 / 2) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 1) (by decide) (lam := 2) (by decide)
  exact h.trans (by norm_num)

-- At x = 1 the Fibonacci polynomials of indices 2 and 4 evaluate to 1 and 3.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔣 (2 * n + 2)) ^ 2 -
    1 / aeval (1 : ℝ) (𝔣 (2 * n + 2 + 4)) ^ 2) = 10 / 9 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_even (x := 1) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 2) (by decide) (lam := 2) (by decide)
  have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial])

-- At x = 1/2 the Lucas polynomials of indices 2 and 4 evaluate to 9/4 and 49/16.
example : ∑' n : ℕ, (1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 2)) -
    1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 2 + 4))) = 340 / 441 := by
  have h := tsum_inv_pow_gibonacciPoly_sub_even (x := 1 / 2) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 2) (by decide) (lam := 1) (by decide)
  have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  simp only [pow_one] at h
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial, map_ofNat])

-- The empty initial block has sum zero for either polynomial family.
example {x : ℝ} (hx : 0 < x) {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩)
    {lam : ℕ} (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 2)) ^ lam - 1 / aeval x (g (2 * n + 2)) ^ lam) = 0 := by
  simpa only [Nat.mul_zero, Nat.add_zero, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
    Finset.sum_empty] using tsum_inv_pow_gibonacciPoly_sub_even hx hg (k := 0) (by decide) hlam

-- At x = 1 the first two odd-index Fibonacci values are 1 and 2.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔣 (2 * n + 1)) ^ 2 -
    1 / aeval (1 : ℝ) (𝔣 (2 * n + 1 + 4)) ^ 2) = 5 / 4 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_even (x := 1) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 2) (by decide) (lam := 2) (by decide)
  have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial])

-- At x = 1/2 the first two odd-index Lucas values are 1/2 and 13/8.
example : ∑' n : ℕ, (1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1)) -
    1 / aeval (1 / 2 : ℝ) (𝔩 (2 * n + 1 + 4))) = 34 / 13 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_even (x := 1 / 2) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 2) (by decide) (lam := 1) (by decide)
  have hIcc : Finset.Icc 1 (2 : ℕ) = {1, 2} := by decide
  simp only [pow_one] at h
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial, map_ofNat])

-- At shift zero the odd-index series has an empty initial block.
example {x : ℝ} (hx : 0 < x) {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩)
    {lam : ℕ} (hlam : 0 < lam) :
    ∑' n : ℕ, (1 / aeval x (g (2 * n + 1)) ^ lam - 1 / aeval x (g (2 * n + 1)) ^ lam) = 0 := by
  simpa only [Nat.mul_zero, Nat.add_zero, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1),
    Finset.sum_empty] using tsum_inv_pow_gibonacciPoly_succ_sub_even hx hg (k := 0) (by decide) hlam

-- The zero shift gives zero at every index for both sequences.
example (n : ℕ) : 𝔣 n * 𝔣 n - 𝔣 n ^ 2 = 0 ∧ 𝔩 n * 𝔩 n - 𝔩 n ^ 2 = 0 := by
  simpa using gibonacciPoly_mul_sub_sq (n := n) (k := 0) (Nat.zero_le n)

-- At n = k = 2 the lower index is zero, and n + k is even.
example : 𝔣 4 * 𝔣 0 - 𝔣 2 ^ 2 = -(X ^ 2) ∧
    𝔩 4 * 𝔩 0 - 𝔩 2 ^ 2 = (X ^ 2 + 4) * X ^ 2 := by
  have hf₂ : 𝔣 2 = X := by simp
  simpa only [Nat.reduceAdd, Nat.reduceSub, hf₂, (by norm_num : (-1 : ℤ[X]) ^ (5 : ℕ) = -1),
    (by norm_num : (-1 : ℤ[X]) ^ (4 : ℕ) = 1), neg_one_mul, one_mul] using
    gibonacciPoly_mul_sub_sq (n := 2) (k := 2) (by decide)

-- At n = 3, k = 2 the lower index is positive and both signs are reversed.
example : 𝔣 5 * 𝔣 1 - 𝔣 3 ^ 2 = X ^ 2 ∧
    𝔩 5 * 𝔩 1 - 𝔩 3 ^ 2 = -(X ^ 2 + 4) * X ^ 2 := by
  have hf₂ : 𝔣 2 = X := by simp
  simpa only [Nat.reduceAdd, Nat.reduceSub, hf₂, (by norm_num : (-1 : ℤ[X]) ^ (6 : ℕ) = 1),
    (by norm_num : (-1 : ℤ[X]) ^ (5 : ℕ) = -1), neg_one_mul, one_mul] using
    gibonacciPoly_mul_sub_sq (n := 3) (k := 2) (by decide)

-- The smallest odd shift keeps just the Fibonacci term of index 2, which evaluates to 2.
example : ∑' n : ℕ, (1 / aeval (2 : ℝ) (𝔣 (2 * n + 2)) ^ 1 -
    1 / aeval (2 : ℝ) (𝔣 (2 * n + 2 + 2)) ^ 1) = 1 / 2 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_odd (x := 2) (by norm_num) (g := 𝔣)
    (Or.inl rfl) (k := 1) (by decide) (lam := 1) (by decide)
  exact h.trans (by norm_num [generalizedFibonacciPolynomial])

-- A shift of three keeps the Lucas terms at 2, 4 and 6, which evaluate to 3, 7 and 18.
example : ∑' n : ℕ, (1 / aeval (1 : ℝ) (𝔩 (2 * n + 2)) ^ 2 -
    1 / aeval (1 : ℝ) (𝔩 (2 * n + 2 + 6)) ^ 2) = 1 / 9 + 1 / 49 + 1 / 324 := by
  have h := tsum_inv_pow_gibonacciPoly_succ_sub_odd (x := 1) (by norm_num) (g := 𝔩)
    (Or.inr rfl) (k := 3) (by decide) (lam := 2) (by decide)
  have hIcc : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  exact h.trans (by norm_num [hIcc, generalizedFibonacciPolynomial, map_ofNat])
