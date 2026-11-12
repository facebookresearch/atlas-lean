/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Risk.ArrowPratt
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Risk.ArrowPratt`

CRRA with `γ = 2` has relative risk aversion `2` and absolute risk aversion `γ / x = 1/2` at `x =
4`; CARA with `a = 3` has absolute risk aversion `3`; the log case has relative risk aversion `1`.
-/

open MathlibExt.Economics.Risk
open Real

namespace MathlibExtTest.Economics.Risk.ArrowPratt

example : relativeRiskAversion (crraUtility 2) 3 = 2 :=
  relativeRiskAversion_crraUtility 2 (show (0:ℝ) < 3 by norm_num)

example : absoluteRiskAversion (crraUtility 2) 4 = 1 / 2 := by
  have h := relativeRiskAversion_crraUtility 2 (show (0:ℝ) < 4 by norm_num)
  simp only [relativeRiskAversion] at h
  linarith

example : absoluteRiskAversion (caraUtility 3) 5 = 3 :=
  absoluteRiskAversion_caraUtility 3 5

example : relativeRiskAversion (crraUtility 1) 7 = 1 :=
  relativeRiskAversion_crraUtility 1 (show (0:ℝ) < 7 by norm_num)

end MathlibExtTest.Economics.Risk.ArrowPratt
