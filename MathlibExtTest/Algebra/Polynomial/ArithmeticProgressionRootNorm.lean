/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ArithmeticProgressionRootNorm
import Mathlib.Tactic.NormNum

open Polynomial

namespace MetaMathlibExt

-- For (m, a, d) = (3, 18, 13), the bound is attained by a root at -3/2.
example : ‖((-3 / 2 : ℝ) : ℂ)‖ ≤ (3 / 2 : ℝ) := by
  have hz : aeval ((-3 / 2 : ℝ) : ℂ)
      (∑ i ∈ Finset.range (3 + 1), C ((18 : ℤ) + i * 13) * X ^ (3 - i)) = 0 := by
    simp only [map_sum, map_mul, map_pow, aeval_C, aeval_X]
    norm_num [Finset.sum_range_succ]
  exact (arithProgPoly_root_norm_le (m := 3) (a := 18) (d := 13)
    (by decide) (by decide) (by decide) (3 / 2) (by norm_num) (by norm_num) _ hz).1

-- A root on the same circle is forced to be that negative real number.
example (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (3 + 1), C ((18 : ℤ) + i * 13) * X ^ (3 - i)) = 0)
    (hn : ‖z‖ = (3 / 2 : ℝ)) : z = -(3 / 2 : ℂ) := by
  have h := (arithProgPoly_root_norm_le (m := 3) (a := 18) (d := 13)
    (by decide) (by decide) (by decide) (3 / 2) (by norm_num) (by norm_num) z hz).2 hn
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using h

end MetaMathlibExt
