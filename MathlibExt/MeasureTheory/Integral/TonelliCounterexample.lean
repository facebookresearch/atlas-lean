/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Tonelli's theorem fails without σ-finiteness

Tonelli's theorem (Mathlib's `MeasureTheory.lintegral_lintegral_swap` and
`MeasureTheory.lintegral_prod`) lets one exchange the order of integration of a nonnegative
measurable function on a product of σ-finite (indeed s-finite) measure spaces. Without that
hypothesis it fails, already for the indicator of the diagonal of `[0, 1]²`, a closed and hence
measurable set: with Lebesgue measure `m` on the first factor and counting measure `#` on the
second,

`∫ (∫ 1_{x = y} d#(y)) dm(x) = ∫ 1 dm = 1` but `∫ (∫ 1_{x = y} dm(x)) d#(y) = ∫ 0 d# = 0`.

As a consequence, counting measure on `[0, 1]` is not s-finite.

Both factors carry the Borel σ-algebra of `ℝ` (restricted to `[0, 1]` by the measures). Tao's
exercise uses the Lebesgue σ-algebra on the first factor and the discrete σ-algebra on the second;
the diagonal is Borel, so the version here is slightly stronger. Tao's further part, the
non-uniqueness of the product measure, is not formalised.

## Main results

* `MeasureTheory.lintegral_lintegral_count_indicator_diagonal`: the first iterated integral is `1`.
* `MeasureTheory.lintegral_count_lintegral_indicator_diagonal`: the second iterated integral is `0`.
* `MeasureTheory.not_sFinite_count_restrict_Icc`: counting measure on `[0, 1]` is not s-finite.

## References

* T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, AMS, 2011,
  Exercise 1.7.22 (Tonelli's theorem can fail without σ-finiteness).
-/

@[expose] public section

open Set

namespace MeasureTheory

/-- The section of the diagonal indicator at `x` is the indicator of `{x}`. -/
private lemma indicator_diagonal_left (x : ℝ) :
    (fun y : ℝ => (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) =
      ({x} : Set ℝ).indicator 1 := by
  ext y
  by_cases h : x = y
  · subst h; simp
  · have h' : y ∉ ({x} : Set ℝ) := fun hy => h (mem_singleton_iff.mp hy).symm
    simp [indicator_of_notMem h', indicator_of_notMem (show (x, y) ∉ diagonal ℝ from h)]

/-- The section of the diagonal indicator at `y` is the indicator of `{y}`. -/
private lemma indicator_diagonal_right (y : ℝ) :
    (fun x : ℝ => (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) =
      ({y} : Set ℝ).indicator 1 := by
  ext x
  by_cases h : x = y
  · subst h; simp
  · have h' : x ∉ ({y} : Set ℝ) := fun hx => h (mem_singleton_iff.mp hx)
    simp [indicator_of_notMem h', indicator_of_notMem (show (x, y) ∉ diagonal ℝ from h)]

/-- **Integrating the diagonal first against counting measure** (Tao, *An Introduction to
Measure Theory*, Exercise 1.7.22). For the indicator of the diagonal of `[0, 1]²`,
`∫_{[0,1]} (∫_{[0,1]} 1_{x = y} d#(y)) dm(x) = 1`, where `#` is counting measure and `m` is
Lebesgue measure: the inner integral is `#{x} = 1` for every `x ∈ [0, 1]`. -/
theorem lintegral_lintegral_count_indicator_diagonal :
    ∫⁻ x in Icc (0 : ℝ) 1, (∫⁻ y in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y) ∂Measure.count) = 1 := by
  have h : ∀ x ∈ Icc (0 : ℝ) 1, ∫⁻ y in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y) ∂Measure.count = 1 := by
    intro x hx
    rw [indicator_diagonal_left, lintegral_indicator_one (measurableSet_singleton x),
      Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_mem hx,
      Measure.count_singleton]
  rw [setLIntegral_congr_fun measurableSet_Icc h]
  simp

/-- **Integrating the diagonal first against Lebesgue measure** (Tao, *An Introduction to
Measure Theory*, Exercise 1.7.22). For the indicator of the diagonal of `[0, 1]²`,
`∫_{[0,1]} (∫_{[0,1]} 1_{x = y} dm(x)) d#(y) = 0`: the inner integral is `m{y} = 0`. -/
theorem lintegral_count_lintegral_indicator_diagonal :
    ∫⁻ y in Icc (0 : ℝ) 1, (∫⁻ x in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y)) ∂Measure.count = 0 := by
  have h : ∀ y : ℝ, ∫⁻ x in Icc (0 : ℝ) 1,
      (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y) = 0 := by
    intro y
    rw [indicator_diagonal_right, lintegral_indicator_one (measurableSet_singleton y)]
    rw [Measure.restrict_apply (measurableSet_singleton y)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  simp [h]

/-- **Counting measure on `[0, 1]` is not s-finite.** Otherwise Tonelli's theorem
(`lintegral_lintegral_swap`) would make the two iterated integrals of the (measurable) indicator
of the diagonal equal, but they are `1` and `0`. -/
theorem not_sFinite_count_restrict_Icc :
    ¬ SFinite ((Measure.count : Measure ℝ).restrict (Icc 0 1)) := by
  intro hs
  have hmeas : Measurable ((diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal)) :=
    measurable_one.indicator measurableSet_diagonal
  have := lintegral_lintegral_swap (μ := volume.restrict (Icc (0 : ℝ) 1))
    (ν := (Measure.count : Measure ℝ).restrict (Icc 0 1))
    (f := fun x y => (diagonal ℝ).indicator (1 : ℝ × ℝ → ENNReal) (x, y))
    hmeas.aemeasurable
  rw [lintegral_lintegral_count_indicator_diagonal,
    lintegral_count_lintegral_indicator_diagonal] at this
  exact one_ne_zero this

end MeasureTheory
