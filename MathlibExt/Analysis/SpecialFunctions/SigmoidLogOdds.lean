/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The logistic function of a log ratio

`Real.sigmoid_log_sub_log`: for `a, b > 0`, `sigmoid (log a - log b) = a / (a + b)`. A two-class
posterior `a / (a + b)` is thus the logistic function of the log odds.
-/

@[expose] public section

namespace Real

/-- **The logistic function of the log odds.** For real numbers $a > 0$ and $b > 0$, the logistic
function $\sigma(z) = 1 / (1 + e^{-z})$ satisfies $\sigma(\log a - \log b) = a / (a + b)$. -/
theorem sigmoid_log_sub_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    sigmoid (log a - log b) = a / (a + b) := by
  rw [sigmoid_def, neg_sub, exp_sub, exp_log hb, exp_log ha]
  field_simp

end Real
