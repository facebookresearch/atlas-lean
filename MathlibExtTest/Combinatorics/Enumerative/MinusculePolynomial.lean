/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MinusculePolynomial

open MetaMathlibExt Polynomial

-- At n = 0 the interval in the defining sum is empty.
example : minusculePolynomialA 0 = 0 := by
  simp [minusculePolynomialA]

-- At x = -1 the first exponential has argument zero.
example (z : ℝ) :
    HasSum (fun n : ℕ => aeval (1 : ℝ) (minusculePolynomialA n) * z ^ n / n.factorial)
      (1 / 8 + (4 * z - 1) / 8 * Real.exp (4 * z)) := by
  have h := minusculePolynomialA_egf (-1) z (by norm_num)
  norm_num at h
  convert h using 1
  ring
