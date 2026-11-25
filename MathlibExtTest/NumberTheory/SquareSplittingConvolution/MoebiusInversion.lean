/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolution.MoebiusInversion

open MetaMathlibExt

variable (m f F : ArithmeticFunction ℂ)
  (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)

-- At a prime square the inverse subtracts the term at 1, skipping the prime.
example (hF : F = squareSplitConv ArithmeticFunction.zeta f) : f 4 = F 4 - F 1 := by
  have h₁ := DFunLike.congr_fun hm 1
  simp [squareSplitConv_apply, squareSplitDivisors_one] at h₁
  have hA : squareSplitDivisors 4 = {1, 4} := by decide +kernel
  have h₄ := DFunLike.congr_fun hm 4
  simp [squareSplitConv_apply, hA, h₁] at h₄
  have hinv := (squareSplit_moebius_inversion m hm f F).mp hF
  simpa [squareSplitConv_apply, hA, h₁, eq_neg_of_add_eq_zero_left h₄, sub_eq_add_neg]
    using DFunLike.congr_fun hinv 4

-- At a prime cube both squarefree choices occur with both square-root choices.
example (hf : f = squareSplitConv m F) : F 8 = f 8 + (f 4 + (f 2 + f 1)) := by
  have hA : squareSplitDivisors 8 = {1, 2, 4, 8} := by decide +kernel
  have hsum := (squareSplit_moebius_inversion m hm f F).mpr hf
  simpa [squareSplitConv_apply, hA] using DFunLike.congr_fun hsum 8

-- At (1, 1) each divisor sum has exactly one term.
example (a b : ArithmeticFunction ℂ) : squareSplitConv a b 1 = a 1 * b 1 := by
  simpa using squareSplitConv_bivariate_iso.1 a b 1 1 squarefree_one (by decide)

-- The two coordinates can share a prime; the four pairs still give four terms.
example (a b : ArithmeticFunction ℂ) :
    squareSplitConv a b 8 = a 8 * b 1 + a 2 * b 4 + (a 4 * b 2 + a 1 * b 8) := by
  have hd : (2 : ℕ).divisors = {2, 1} := by decide +kernel
  simpa [hd] using squareSplitConv_bivariate_iso.1 a b 2 2 Nat.prime_two.squarefree (by decide)

-- The interpolant reads arbitrary data at shared coordinates, but always vanishes at zero.
example (G : ℕ → ℕ → ℂ) : ∃ a : ArithmeticFunction ℂ, a 216 = G 6 6 ∧ a 0 = 0 := by
  obtain ⟨a, ha, _⟩ := squareSplitConv_bivariate_iso.2 G
  have hu : Squarefree (6 : ℕ) := by decide +kernel
  exact ⟨a, ha 6 6 hu (by decide), by simp⟩
