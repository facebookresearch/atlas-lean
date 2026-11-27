/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# Tests for the dyadic maximal function

Non-vacuity checks: for `f = 1_{[0,1)}` the hypotheses of the Calderón–Zygmund decomposition
hold, the set `{M_d f > 1/2}` contains `0`, and `0` has a stopping level at height `1/2`.
Non-vacuity of the `L^p` bound: `M_d 1_{[0,1)}` is square integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.Analysis.HarmonicAnalysis.DyadicMaximal

open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-- The indicator of the unit interval. -/
noncomputable abbrev f₀ : ℝ → ℝ := (Ico (0 : ℝ) 1).indicator fun _ => 1

example : dyadicIndex 0 (1 / 2 : ℝ) = 0 := by
  rw [dyadicIndex, Int.floor_eq_iff]
  norm_num

example : (3 / 4 : ℝ) ∈ dyadicInterval 2 3 := by
  rw [dyadicInterval, mem_Ico]
  constructor <;> norm_num

example : dyadicInterval 0 0 = Ico (0 : ℝ) 1 := by
  simp [dyadicInterval]

theorem lintegral_f₀ : ∫⁻ y, ‖f₀ y‖ₑ = 1 := by
  rw [show (fun y => ‖f₀ y‖ₑ) = (Ico (0 : ℝ) 1).indicator fun _ => (1 : ℝ≥0∞) by
    ext y; by_cases hy : y ∈ Ico (0 : ℝ) 1 <;> simp [f₀, hy]]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, Real.volume_Ico]
  simp

theorem dyadicAverage_f₀ : dyadicAverage 0 f₀ 0 = 1 := by
  have hI : dyadicInterval 0 (dyadicIndex 0 0) = Ico (0 : ℝ) 1 := by
    simp [dyadicInterval, dyadicIndex]
  rw [dyadicAverage, hI, setLAverage_eq,
    setLIntegral_congr_fun measurableSet_Ico (g := fun _ => (1 : ℝ≥0∞))
      (fun y hy => by simp [f₀, hy]),
    setLIntegral_const, one_mul, Real.volume_Ico]
  simp

example : (1 / 2 : ℝ≥0∞) < dyadicMaximalFunction f₀ 0 := by
  refine lt_of_lt_of_le ?_ (le_iSup (fun k : ℤ => dyadicAverage k f₀ 0) 0)
  rw [dyadicAverage_f₀]
  exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top

/-- The Calderón–Zygmund hypotheses are jointly satisfiable and its conclusion is not vacuous. -/
example : ∃ k, IsStoppingLevel f₀ (1 / 2) 0 k := by
  refine exists_isStoppingLevel (by rw [lintegral_f₀]; exact ENNReal.one_ne_top)
    (by simp) ?_
  refine lt_of_lt_of_le ?_ (le_iSup (fun k : ℤ => dyadicAverage k f₀ 0) 0)
  rw [dyadicAverage_f₀]
  exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top

example : (1 / 2 : ℝ≥0∞) * volume {x | 1 / 2 < dyadicMaximalFunction f₀ x} ≤ 1 := by
  simpa [lintegral_f₀] using dyadicMaximalFunction_mul_volume_le_lintegral f₀ (1 / 2)

example : ∀ᵐ x, dyadicMaximalFunction f₀ x ≤ 1 / 2 → ‖f₀ x‖ₑ ≤ 1 / 2 :=
  (calderon_zygmund (f := f₀)
    (measurable_const.indicator measurableSet_Ico).enorm.aemeasurable
    (by rw [lintegral_f₀]; exact ENNReal.one_ne_top)
    (by simp)).2.1

theorem lintegral_f₀_sq : ∫⁻ y, ‖f₀ y‖ₑ ^ (2 : ℝ) = 1 := by
  rw [show (fun y => ‖f₀ y‖ₑ ^ (2 : ℝ)) = (Ico (0 : ℝ) 1).indicator fun _ => (1 : ℝ≥0∞) by
    ext y; by_cases hy : y ∈ Ico (0 : ℝ) 1 <;> simp [f₀, hy]]
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, Real.volume_Ico]
  simp

/-- The sharp `L^2` bound applies to `1_{[0,1)}` and shows that `M_d 1_{[0,1)}` is square
integrable. -/
example : ∫⁻ x, dyadicMaximalFunction f₀ x ^ (2 : ℝ) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_rpow_dyadicMaximalFunction_le
    (measurable_const.indicator measurableSet_Ico).enorm.aemeasurable (by norm_num : (1 : ℝ) < 2))
  rw [lintegral_f₀_sq, mul_one]
  exact ENNReal.ofReal_ne_top

/-- Dyadic Lebesgue differentiation applies to the indicator of the unit interval. -/
example : ∀ᵐ x, Filter.Tendsto
    (fun n : ℕ => ⨍ y in dyadicInterval n (dyadicIndex n x), f₀ y) Filter.atTop
      (nhds (f₀ x)) :=
  ae_tendsto_setAverage_dyadicInterval
    ((locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ico)

end MathlibExtTest.Analysis.HarmonicAnalysis.DyadicMaximal
