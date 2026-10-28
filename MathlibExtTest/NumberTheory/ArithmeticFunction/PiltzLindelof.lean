/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.PiltzLindelof
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Tests for the Piltz divisor problem
-/

@[expose] public section

open ArithmeticFunction

example : piltz 3 12 ≤ sigma 0 12 ^ 3 := piltz_le_sigma_zero_pow 3 12

example : ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, (piltz 3 n : ℝ) ≤ A * (n : ℝ) ^ (1 / 4 : ℝ) :=
  exists_piltz_le_mul_rpow 3 (by norm_num)

-- `k = 0`: `d_0 = δ`, whose L-series is `1 = ζ^0`.
example (s : ℂ) (hs : 1 < s.re) : LSeries (fun n : ℕ => (piltz 0 n : ℂ)) s = 1 := by
  simpa using LSeries_piltz 0 hs

-- `∑ d(n) / n² = ζ(2)² = π⁴ / 36`.
example : LSeries (fun n : ℕ => (piltz 2 n : ℂ)) 2 = (Real.pi : ℂ) ^ 4 / 36 := by
  rw [LSeries_piltz 2 (by norm_num), riemannZeta_two]
  ring

example : LSeriesSummable (fun n : ℕ => (piltz 5 n : ℂ)) 2 :=
  LSeriesSummable_piltz 5 (by norm_num)
