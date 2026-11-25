/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.NumberTheory.CatalanOddMultipleHarmonicDivTsum

open MetaMathlibExt

-- At depth one the zeta value is $\zeta(2) = \pi^2 / 6$, so the sum is
-- $3 \zeta(2) - 4 = \pi^2 / 2 - 4$.
example : ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic 1 n / (4 ^ n * n) : ℝ) : ℂ) =
    (Real.pi : ℂ) ^ 2 / 2 - 4 := by
  have hzeta : riemannZeta (((1 : ℕ) : ℂ) + 1) = (Real.pi : ℂ) ^ 2 / 6 := by
    convert riemannZeta_two using 2
    norm_num
  rw [catalan_oddMultipleHarmonic_div_tsum 1 one_pos, hzeta]
  ring

-- The theorem applies at every positive depth.
example (k : ℕ) (hk : 0 < k) :
    ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * n) : ℝ) : ℂ) =
      (2 ^ (k + 1) - 1) * riemannZeta (k + 1) - 2 ^ (k + 1) :=
  catalan_oddMultipleHarmonic_div_tsum k hk
