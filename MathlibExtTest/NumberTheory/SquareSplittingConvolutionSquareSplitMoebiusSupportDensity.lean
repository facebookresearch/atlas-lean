/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusSupportDensity

/-!
# Tests for the support of the square-splitting Möbius function

The support theorem includes the prime cube eight and excludes the fourth power sixteen.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 11.
-/

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusSupportDensity

open MetaMathlibExt

example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) : m 8 ≠ 0 := by
  apply ((squareSplitMoebius_support_density m hm).1 8 (by decide)).mpr
  intro p
  change (2 ^ 3).factorization p ≤ 3
  rw [Nat.prime_two.factorization_pow, Finsupp.single_apply]
  split_ifs <;> omega

example (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1) : m 16 = 0 := by
  by_contra h
  have hb := ((squareSplitMoebius_support_density m hm).1 16 (by decide)).mp h 2
  have hf : (16 : ℕ).factorization 2 = 4 := by
    change (2 ^ 4).factorization 2 = 4
    rw [Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  rw [hf] at hb
  omega

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitMoebiusSupportDensity
