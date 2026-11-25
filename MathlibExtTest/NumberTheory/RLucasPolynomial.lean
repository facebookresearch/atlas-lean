/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RLucasPolynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for partial sums of the r-Lucas polynomials -/

open MetaMathlibExt

-- At n = r - 1 the final window includes V₀ = s + 1.
example : ∑ j ∈ Finset.Icc 1 2, rLucasPolynomial 3 4 (2 : ℚ) 3 j = 6 := by
  rw [sum_rLucasPolynomial (by decide) (by decide) (by decide) _ _ _ (by norm_num)]
  have h (i : ℕ) (hi : i < 3) :
      rLucasPolynomial 3 4 (2 : ℚ) 3 (i + 1) = 2 ^ (i + 1) :=
    rLucasPolynomial_succ_of_lt _ _ _ hi
  norm_num [show Finset.Icc 1 3 = {1, 2, 3} by decide, rLucasPolynomial_zero,
    h 0 (by decide), h 1 (by decide), h 2 (by decide)]

-- For the classical Lucas numbers the first n terms from index one sum to L_(n+2) - 3.
example {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, rLucasPolynomial 1 1 (1 : ℚ) 1 j =
      rLucasPolynomial 1 1 (1 : ℚ) 1 (n + 2) - 3 := by
  rw [sum_rLucasPolynomial (by decide) hn (by omega) _ _ _ (by norm_num),
    rLucasPolynomial_succ_of_le (n := n + 1) 1 1 1 (by omega)]
  simp
  ring
