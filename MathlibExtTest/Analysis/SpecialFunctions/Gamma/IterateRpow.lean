/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.Analysis.SpecialFunctions.Gamma.IterateRpow

open MetaMathlibExt Real

-- At the minimum base and first admissible index, both steps are ordinary exponentials.
example : exp (exp (exp 1)) < Gamma (exp (exp 1)) := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, exp_one_rpow] using
    iterate_rpow_succ_lt_Gamma_iterate_rpow (hb := le_rfl) (hn := Nat.one_pos)

-- At index two, Gamma is applied to the second iterate from the base.
example : (3 : ℝ) ^ ((3 : ℝ) ^ (27 : ℝ)) < Gamma ((3 : ℝ) ^ (27 : ℝ)) := by
  have hfirst : (3 : ℝ) ^ (3 : ℝ) = 27 := by norm_num [rpow_ofNat]
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, hfirst] using
    iterate_rpow_succ_lt_Gamma_iterate_rpow (hb := exp_one_lt_three.le)
      (hn := show 0 < 2 by decide)
