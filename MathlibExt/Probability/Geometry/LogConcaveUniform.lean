/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Geometry.ThinShell
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability

/-!
# Actual uniform log-concave laws

Source: `constants/20b.md`, uniform convex-body laws, and the elementary
interval moment formulas used for the cube examples in `constants/20a.md`.
-/

@[expose] public section

namespace MathlibExt.Probability.ThinShell

open MeasureTheory
open scoped ENNReal

/-- A positive constant density on a measurable convex set is log-concave.
Source: the uniform convex-body example in `constants/20b.md`. -/
theorem isLogConcaveDensity_indicator_const {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hm : MeasurableSet K) {c : ℝ} (hc : 0 < c) :
    IsLogConcaveDensity (K.indicator (fun _ => c)) := by
  classical
  have hn : ∀ x, 0 ≤ K.indicator (fun _ => c) x := by
    intro x
    by_cases hx : x ∈ K <;> simp [hx, hc.le]
  refine ⟨measurable_const.indicator hm, hn, ?_⟩
  intro x y t ht ht1
  simp only [Real.rpow_eq_pow]
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hK hx hy (show 0 ≤ 1 - t by linarith) ht.le (by ring)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
    · simp only [Set.indicator_of_notMem hy, Real.zero_rpow ht.ne', mul_zero]
      exact hn _
  · have h : 1 - t ≠ 0 := by linarith
    simp only [Set.indicator_of_notMem hx, Real.zero_rpow h, zero_mul]
    exact hn _

/-- Conditioning on a finite-volume set gives its actual normalized density.
Source: `constants/20b.md`, normalized Lebesgue law on a convex body. -/
theorem cond_eq_withDensity_indicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {K : Set α} (hm : MeasurableSet K) (hK : μ K ≠ 0) :
    ProbabilityTheory.cond μ K =
      μ.withDensity (fun x => ENNReal.ofReal
        (K.indicator (fun _ => (μ K)⁻¹.toReal) x)) := by
  classical
  have hf : (fun x => ENNReal.ofReal (K.indicator (fun _ => (μ K)⁻¹.toReal) x)) =
      K.indicator (fun _ => (μ K)⁻¹) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hK)]
    · simp [hx]
  rw [hf, withDensity_indicator hm, withDensity_const]
  rfl

end MathlibExt.Probability.ThinShell
