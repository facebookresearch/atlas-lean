/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCPositivity

/-! # Tests for `MathlibExt.Algebra.Polynomial.ChebyshevCPositivity` -/

namespace MathlibExtTest.ChebyshevCPositivity

open Polynomial MetaMathlibExt

/-- `T̄_3 = X ^ 3 - 3 X`, from `T̄_1 = X`, `T̄_2 = X ^ 2 - 2` and the recurrence. -/
private theorem chebyshevC_three : Chebyshev.C ℝ 3 = X ^ 3 - 3 * X := by
  rw [show (3 : ℤ) = 1 + 2 by norm_num, Chebyshev.C_add_two]
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, Chebyshev.C_two, Chebyshev.C_one]
  ring

-- At the endpoint `x = 2` every value is `T̄_k(2) = 2`, and the theorem applies there.
example (k : ℕ) : 0 < (Chebyshev.C ℝ k).eval 2 := chebyshevC_eval_pos_of_two_le k 2 le_rfl

example (k : ℕ) : (Chebyshev.C ℝ k).eval 2 = 2 := Chebyshev.C_eval_two ℝ k

-- With `k = 3` the theorem says `x ^ 3 - 3 x > 0` for every real `x ≥ 2`.
example (x : ℝ) (hx : 2 ≤ x) : 0 < x ^ 3 - 3 * x := by
  simpa [chebyshevC_three] using chebyshevC_eval_pos_of_two_le 3 x hx

-- The bound `x ≥ 2` cannot be lowered to `x ≥ 3 / 2`: `T̄_3(3 / 2) = 27 / 8 - 9 / 2 < 0`.
example : (Chebyshev.C ℝ ((3 : ℕ) : ℤ)).eval (3 / 2) < 0 := by
  norm_num [chebyshevC_three]

-- Below `2`, positivity already fails for `k = 2`: `T̄_2(1) = 1 - 2 = -1`.
example : (Chebyshev.C ℝ ((2 : ℕ) : ℤ)).eval 1 = -1 := by
  norm_num [Chebyshev.C_two]

-- The integer form used for the Kassel–Reutenauer polynomials: `T̄_k(N) > 0` in `ℤ` for every
-- integer `N ≥ 2`, by mapping `T̄_k ∈ ℤ[X]` to `ℝ[X]`.
example (k : ℕ) (N : ℤ) (hN : 2 ≤ N) : 0 < (Chebyshev.C ℤ k).eval N := by
  have h := chebyshevC_eval_pos_of_two_le k N (by exact_mod_cast hN)
  rw [← Chebyshev.map_C (Int.castRingHom ℝ), eval_intCast_map, eq_intCast] at h
  exact_mod_cast h

end MathlibExtTest.ChebyshevCPositivity
