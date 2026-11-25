/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPFibonacciSum

open MetaMathlibExt MathlibExt.NumberTheory.LeonardoPWanted

-- The shortest window at the first allowed index also permits k = 0.
example : ∑ i ∈ Finset.range 2, (fibonacciP 1 (1 + i) : ℤ) = 2 := by
  calc
    _ = leonardoPK 1 0 2 := by simpa using succ_mul_sum_fibonacciP 1 0 1 (by decide) (by decide)
    _ = 2 := by decide

-- For p = 3 the four terms starting at index four correspond to Leonardo index nine.
example : 3 * ∑ i ∈ Finset.range 4, (fibonacciP 3 (4 + i) : ℤ) = 30 := by
  calc
    _ = leonardoPK 3 2 9 + 2 := succ_mul_sum_fibonacciP 3 2 4 (by decide) (by decide)
    _ = 30 := by decide
