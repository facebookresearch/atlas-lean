/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReciprocalSineSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the reciprocal sine bound -/

namespace MathlibExtTest.ReciprocalSineSum

open Finset MetaMathlibExt

-- The smallest prime and interval allowed by the hypotheses.
example :
    1 / |Real.sin (Real.pi / 3)| <
      (3 / Real.pi) * (Real.eulerMascheroniConstant + 1 / 2) + 3 / (4 * Real.pi) := by
  have h := sum_one_div_abs_sin_lt 3 (by decide) 1 (by decide) 1 (by decide) (by norm_num)
  norm_num [Icc_self] at h ⊢
  convert h using 1
  ring

-- A negative multiplier permutes the three least absolute representatives
-- at the largest admissible length for the prime 7.
example :
    ∑ h ∈ Icc (1 : ℕ) 3, 1 / |Real.sin (Real.pi * (-2) * (h : ℝ) / 7)| <
      (7 / Real.pi) * (Real.log 3 + Real.eulerMascheroniConstant + 1 / 6) +
        21 / (10 * Real.pi) := by
  have h := sum_one_div_abs_sin_lt 7 (by decide) (-2) (by decide) 3 (by decide) (by norm_num)
  norm_num at h ⊢
  convert h using 1
  ring

end MathlibExtTest.ReciprocalSineSum
