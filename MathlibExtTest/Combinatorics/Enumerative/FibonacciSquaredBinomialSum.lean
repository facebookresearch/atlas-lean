/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibonacciSquaredBinomialSum

/-! # Tests for the double binomial sum of squared Fibonacci numbers -/

namespace MathlibExtTest.FibonacciSquaredBinomialSum

open Finset MetaMathlibExt

-- The empty board contributes the single term with i = j = 0.
example : (∑ i ∈ range 1, ∑ j ∈ range (i + 1),
    i.choose j * (0 - 3 * i).choose j * 2 ^ j) = 1 :=
  (fib_succ_sq_eq_sum_choose_mul_choose 0).symm

-- At n = 3 the last inner sum has second upper index zero and contributes one.
example : (∑ i ∈ range 3, ∑ j ∈ range (i + 1),
    i.choose j * (6 - 3 * i).choose j * 2 ^ j) = 9 := by
  decide

-- At n = 4 the last inner sum includes a nonzero j = 2 term.
example : (∑ i ∈ range 3, ∑ j ∈ range (i + 1),
    i.choose j * (8 - 3 * i).choose j * 2 ^ j) = 25 :=
  (fib_succ_sq_eq_sum_choose_mul_choose 4).symm

end MathlibExtTest.FibonacciSquaredBinomialSum
