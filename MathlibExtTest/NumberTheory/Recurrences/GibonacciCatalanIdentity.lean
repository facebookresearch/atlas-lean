/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.GibonacciCatalanIdentity

open MetaMathlibExt

-- The Fibonacci indices and the sign exponent are negative; the correction is subtracted.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    -3 * G (-3) - G (-5) = 4 * G (-4) - (G 0 + G (-2)) := by
  have h := fib_gibonacci_catalan_type_identity (G := G) (hG := hG) (k := -3) (r := -1) (s := -1)
  norm_num [show Int.fib (-4) = -3 by decide, show Int.fib (-3) = 2 by decide] at h
  linear_combination h

-- At an even negative sign exponent the correction is added, with coefficient F(-3)^2 = 4.
example (G : ℤ → ℝ) (hG : ∀ j : ℤ, G (j + 2) = G (j + 1) + G j) :
    5 * G (-1) + G (-7) = -(2 * G (-4)) + 4 * (G (-1) + G (-3)) := by
  have h := fib_gibonacci_catalan_type_identity (G := G) (hG := hG) (k := -2) (r := -3) (s := -2)
  norm_num [show Int.fib (-5) = 5 by decide, show Int.fib (-3) = 2 by decide] at h
  exact h

-- For G(j) = F(j + 1), the first example has a nonzero correction, namely -2.
example : (-1 : ℝ) ^ (-3 : ℤ) * (Int.fib (-1) : ℝ) ^ 2 *
    ((Int.fib 1 : ℝ) + Int.fib (-1)) = -2 := by
  norm_num
