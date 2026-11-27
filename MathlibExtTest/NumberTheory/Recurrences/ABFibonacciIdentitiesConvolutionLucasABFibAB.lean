/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionLucasABFibAB
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Tests for a convolution of (a, b)-Lucas and (a, d)-Fibonacci numbers

A concrete instance and the divided-form corollary of
`MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted.convolution_lucasAB_fibAB`.
-/

namespace MathlibExtTest.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionLucasABFibAB

open MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

-- At Fibonacci/Jacobsthal parameters the scaled convolution is the Lucas difference.
example : (1 - 2 : ℂ) * ∑ i ∈ Finset.Icc 1 2,
    lucasAB 1 1 (2 - i) * fibAB 1 2 i = -3 := by
  have h := (convolution_lucasAB_fibAB 1 1 2 (by norm_num) 2).1
  rw [h]
  norm_num [lucasAB]

-- The source's divided form follows from the scaled identity.
example (a b d : ℂ) (hbd : b ≠ d) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, lucasAB a b (n - i) * fibAB a d i =
      (lucasAB a b (n + 1) - lucasAB a d (n + 1)) / (b - d) := by
  have h := (convolution_lucasAB_fibAB a b d hbd n).1
  rw [eq_div_iff (sub_ne_zero.mpr hbd)]
  linear_combination h

end MathlibExtTest.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionLucasABFibAB
