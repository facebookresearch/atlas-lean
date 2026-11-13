/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.SolowLaw
import Mathlib.Tactic.NormNum

open MathlibExt.Economics.Macro.SolowLaw
/-!
# Tests for the discrete Solow law

Zero saving (`s = 0`): `k' = (1 - delta) * k / ((1 + n) * (1 + g))`, concretely
`360/121`. No growth (`n = g = 0`): `k' = s * f(k) + (1 - delta) * k`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.SolowLaw

/-- **Zero-saving case.** With `s = 0` the law collapses to
`k' = (1 - δ) * k / ((1 + n) * (1 + g))`; concretely,
`δ = 1/10`, `n = g = 1/10`, `k = 4` gives `k' = 360/121`. -/
theorem solow_law_zero_saving_example {f : ℝ → ℝ} :
    ((0 : ℝ) * f 4 + (1 - 1 / 10) * 4) / ((1 + 1 / 10) * (1 + 1 / 10)) =
      360 / 121 := by
  norm_num

/-- **No-growth case.** With `n = g = 0` the denominator is `1`, so
`k' = s * f k + (1 - δ) * k`; concretely, `s = 1/4`, `δ = 1/10`,
`f 4 = 3`, `k = 4` gives `k' = 87/20`. -/
theorem solow_law_no_growth_example {f : ℝ → ℝ} (hf : f 4 = 3) :
    ((1 / 4 : ℝ) * f 4 + (1 - 1 / 10) * 4) / ((1 + 0) * (1 + 0)) =
      87 / 20 := by
  rw [hf]
  norm_num

/-- **End-to-end use of `solow_law`.** Zero-saving economy with
`δ = n = g = 1/10`, `E = 10`, `K = 40`, `F = 30`, `K' = 36`,
`E' = 121/10`: per-effective-worker capital next period is
`36 / (121/10)`, equal to the law's right-hand side at `k = 4`. -/
theorem solow_law_end_to_end_zero_saving {f : ℝ → ℝ} (hf : f 4 = 3) :
    (36 : ℝ) / (121 / 10) =
      ((0 : ℝ) * f 4 + (1 - 1 / 10) * 4) / ((1 + 1 / 10) * (1 + 1 / 10)) := by
  have h :=
    solow_law (f := f) (s := 0) (δ := 1 / 10) (n := 1 / 10) (g := 1 / 10)
      (k := 4) (k' := 36 / (121 / 10)) (K := 40) (K' := 36) (E := 10)
      (E' := 121 / 10) (F := 30)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hf]; norm_num) (by norm_num) rfl
  exact h

/-- **Chained value.** The end-to-end `k'` above is exactly `360/121`. -/
theorem solow_law_zero_saving_value {f : ℝ → ℝ} (hf : f 4 = 3) :
    (36 : ℝ) / (121 / 10) = 360 / 121 := by
  rw [solow_law_end_to_end_zero_saving hf, solow_law_zero_saving_example]
end MathlibExtTest.Economics.Macro.SolowLaw
