/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SuperLeonardoP
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The last initial value and the first recursive term use different branches.
example (p : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) : superLeonardoP p 0 x p = x p := by
  simpa using superLeonardoP_zero_eq p hp x p

example (x : ℕ → ℝ) : superLeonardoP 2 0 x 3 = x 2 + x 0 := by
  rw [superLeonardoP_zero_eq 2 (by decide)]
  norm_num [Finset.sum_range_succ, show fibonacciP 2 1 = 1 by decide +kernel,
    show fibonacciP 2 2 = 1 by decide +kernel]

-- Once the sum reaches its full range, the three initial values have distinct weights.
example (x : ℕ → ℝ) : superLeonardoP 2 0 x 6 = 3 * x 2 + (2 * x 0 + x 1) := by
  rw [superLeonardoP_zero_eq 2 (by decide)]
  norm_num [Finset.sum_range_succ, show fibonacciP 2 3 = 1 by decide +kernel,
    show fibonacciP 2 4 = 2 by decide +kernel, show fibonacciP 2 5 = 3 by decide +kernel]
