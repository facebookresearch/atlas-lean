/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Nominal value, price index, and real value

Nominal value equals price index times the corresponding real-value measure under the
pinned base convention: the price index equals `1` in the base period. An index quoted
on a 100 base must be divided by `100` before use here. Deflating is division by the
price index; reflating is multiplication by it. The theorems are division cancellation
after that convention is fixed; the content is the convention, not the arithmetic.

## Main results

* `nominal_eq_priceIndex_mul_real`: `nominal = priceIndex * realValue nominal priceIndex`.
* `priceIndex_eq_nominal_div_real`: `priceIndex = nominal / real` for nonzero real value.
* `nominalReal_example`: nominal `110` at index `1.1` is real `100`.

## References

* MIT 14.05 Intermediate Macroeconomics, Fall 2024, syllabus (measurement scope).
* Australian Bureau of Statistics, price index theory (index definitions and conventions).
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.NominalRealDeflator

/-- **Deflating.** The real value of a nominal magnitude `nominal` at price index
`priceIndex` is `nominal / priceIndex`. Base convention: the price index equals `1` in
the base period. An index quoted on a 100 base must be divided by `100` before use here. -/
noncomputable def realValue (nominal priceIndex : ℝ) : ℝ := nominal / priceIndex

/-- **Reflating.** The nominal value corresponding to real value `real` at price index
`priceIndex` is `priceIndex * real`. -/
noncomputable def nominalValue (real priceIndex : ℝ) : ℝ := priceIndex * real

/-- **Nominal equals price index times real.** Deflating then reflating recovers the
nominal value, provided the price index is nonzero. This is division cancellation
(`mul_div_cancel₀`); the content is the pinned base convention. -/
theorem nominal_eq_priceIndex_mul_real {nominal priceIndex : ℝ} (hP : priceIndex ≠ 0) :
    nominal = priceIndex * realValue nominal priceIndex := by
  unfold realValue
  exact (mul_div_cancel₀ nominal hP).symm

/-- **Price index equals nominal over real.** Under the same convention, with nonzero real
value, the price index is recovered as `nominal / real`. -/
theorem priceIndex_eq_nominal_div_real {nominal real priceIndex : ℝ} (hR : real ≠ 0)
    (h : nominal = priceIndex * real) : priceIndex = nominal / real := by
  rw [h]
  exact (mul_div_cancel_right₀ priceIndex hR).symm

/-- Concrete deflating: nominal `110` at price index `1.1` is real `100`, and reflating
real `100` at `1.1` gives nominal `110`. -/
theorem nominalReal_example : realValue 110 1.1 = 100 ∧ nominalValue 100 1.1 = 110 := by
  constructor <;> norm_num [realValue, nominalValue]

end MathlibExt.Economics.Macro.NominalRealDeflator
