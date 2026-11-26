/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Calculus.ReciprocalDifferenceSqrtBound

open MathlibExt.Analysis.Calculus.ReciprocalDifferenceSqrtBoundWanted

-- The endpoint x = 1 is included for every admissible a.
example {a : ℝ} (ha : 1 < a) :
    1 / 2 - 1 / (1 + a) ≤ (Real.sqrt a - 1) / (Real.sqrt a + 1) := by
  simpa only [one_add_one_eq_two, mul_one] using
    one_div_one_add_sub_one_div_one_add_mul_le ha (le_refl (1 : ℝ))
