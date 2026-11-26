/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GFPFibCatalan
import Mathlib.Tactic.NormNum

/-! # Boundary and small-index checks for the Fibonacci Catalan identity -/

namespace MetaMathlibExt

open Finset Polynomial

example (d g : ℤ[X]) :
    2 ^ (0 - 1 : ℕ) * generalizedFibonacciPolynomial 0 1 d g 0 =
      ∑ i ∈ range 1, ((0 : ℕ).choose (2 * i + 1) : ℤ[X]) *
        d ^ (0 - 2 * i - 1) * (4 * g + d ^ 2) ^ i :=
  gfp_fib_catalan d g 0

example (d g : ℤ[X]) :
    4 * generalizedFibonacciPolynomial 0 1 d g 3 = 3 * d ^ 2 + (4 * g + d ^ 2) := by
  convert gfp_fib_catalan d g 3 using 1 <;> norm_num [sum_range_succ, Nat.choose]

end MetaMathlibExt
