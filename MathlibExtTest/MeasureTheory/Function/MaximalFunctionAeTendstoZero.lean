/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.MaximalFunctionAeTendstoZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory Filter Set
open scoped Topology
open MathlibExt.MeasureTheory.MaximalFunctionAeTendstoZeroWanted

private noncomputable def sample (n : ℕ) (y : ℝ) : ℝ :=
  if y = 0 then 1 else y / ((n : ℝ) + 1)

private noncomputable def maximal (n : ℕ) (x : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ a b : ℝ, x ∈ Icc a b ∧ Icc a b ⊆ Icc (0 : ℝ) 1 ∧ 0 < b - a ∧
    r = (b - a)⁻¹ * ∫ y in Icc a b, |sample n y|}

-- The inputs do not converge at 0, so this example needs the a.e. hypothesis.
example : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Icc 0 1)),
    Tendsto (fun n => maximal n x) atTop (𝓝 0) := by
  apply ae_tendsto_maximal_zero_of_ae_tendsto_zero_of_bounded sample ?_ ?_ ?_ maximal
    (fun _ _ => rfl)
  · intro n
    exact (Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
      (measurable_id.div_const ((n : ℝ) + 1))).aemeasurable
  · intro n y hy
    have hn : 0 < (n : ℝ) + 1 := by positivity
    by_cases hy0 : y = 0
    · simp [sample, hy0]
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      simpa only [sample, ite_eq_right hy0] using
        (show y / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) 1 from
          ⟨div_nonneg hy.1 hn.le, (div_le_iff₀ hn).2 (by simpa using hy.2.trans hn1)⟩)
  · have hne : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Icc 0 1)), x ≠ 0 := by
      rw [ae_iff]
      have hzero : {x : ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
      rw [hzero]
      exact measure_singleton _
    have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right zero_le_one)
        tendsto_natCast_atTop_atTop
    have hinv := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp hcast
    filter_upwards [hne] with x hx
    simpa only [sample, ite_eq_right hx, div_eq_mul_inv, Function.comp_apply, mul_zero] using
      (tendsto_const_nhds (x := x) (f := atTop)).mul hinv
