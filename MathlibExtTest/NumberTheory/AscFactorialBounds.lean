/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AscFactorialBounds

/-!
# Tests for the rising factorial bounds
-/

open MetaMathlibExt

-- The empty product and both zeroth powers are one.
example : 1 ≤ (1 : ℕ).ascFactorial 0 ∧ (1 : ℕ).ascFactorial 0 ≤ 1 :=
  ascFactorial_bounds_half 0 1 (by decide)

-- At length two the threshold is zero and the product attains its lower bound.
example : 0 ≤ (0 : ℕ).ascFactorial 2 ∧ (0 : ℕ).ascFactorial 2 ≤ 1 :=
  ascFactorial_bounds_half 2 0 (by decide)

-- The even and odd thresholds both first reach four at lengths six and seven.
example : 6 ^ 6 ≤ (4 : ℕ).ascFactorial 6 ∧ (4 : ℕ).ascFactorial 6 ≤ 7 ^ 6 :=
  ascFactorial_bounds_half 6 4 (by decide)

example : 6 ^ 7 ≤ (4 : ℕ).ascFactorial 7 ∧ (4 : ℕ).ascFactorial 7 ≤ 7 ^ 7 :=
  ascFactorial_bounds_half 7 4 (by decide)
