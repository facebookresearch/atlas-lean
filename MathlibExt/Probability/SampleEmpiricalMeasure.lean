/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Empirical measures of a sample

For a sequence of points `x₀, x₁, …` in a measurable space `X`, the empirical measure of the
first `n` points is the probability measure `(1/n) ∑_{i<n} δ_{xᵢ}`. It is the random object of
Sanov's theorem: for an i.i.d. sample from `α`, it converges weakly to `α` (law of large numbers)
and its large deviations are governed by relative entropy.

To obtain a probability measure for every `n`, the case `n = 0` (an empty sample) uses the first
point, that is `δ_{x₀}`; this convention does not affect any limit statement.

## Source

S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010,
Section 3 (Sanov's theorem) (https://math.nyu.edu/~varadhan/LDP/Spring2010.3.pdf), where the
empirical distribution `βₙ = (1/n) ∑_{j=1}^n δ_{xⱼ}` maps `Xⁿ` to the space `M(X)` of probability
measures.

## Main results

* `sampleEmpiricalMeasure x n`: the empirical probability measure of `x₀, …, x_{n-1}`.
* `toMeasure_sampleEmpiricalMeasure`: for `n ≥ 1` it is `(1/n) ∑_{i<n} δ_{xᵢ}`.
* `sampleEmpiricalMeasure_apply`: for `n ≥ 1` and measurable `A`, its mass on `A` is the fraction
  of the first `n` points that lie in `A`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MathlibExt.Probability.SampleEmpiricalMeasure

variable {X : Type*} [MeasurableSpace X]

/-- **Averages of Dirac masses are probability measures.** For `m ≥ 1` the average
`(1/m) ∑_{i<m} δ_{xᵢ}` of Dirac masses is a probability measure. -/
lemma isProbabilityMeasure_average_dirac (x : ℕ → X) {m : ℕ} (hm : m ≠ 0) :
    IsProbabilityMeasure ((m : ℝ≥0∞)⁻¹ • ∑ i ∈ range m, Measure.dirac (x i)) := by
  constructor
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hm) (ENNReal.natCast_ne_top m)

/-- **Empirical measure of a sample.** For points `x₀, x₁, …` of `X` and `n ≥ 1`, the
probability measure `(1/n) ∑_{i<n} δ_{xᵢ}`; for `n = 0` it is `δ_{x₀}`. This is the empirical
distribution of Sanov's theorem (Varadhan, *Large Deviations*, NYU lecture notes, 2010,
Section 3). -/
noncomputable def sampleEmpiricalMeasure (x : ℕ → X) (n : ℕ) : ProbabilityMeasure X :=
  ⟨((max n 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ i ∈ range (max n 1), Measure.dirac (x i),
    isProbabilityMeasure_average_dirac x (by omega)⟩

/-- **Empirical measure as an average of Dirac masses.** For `n ≥ 1`, the empirical measure of
`x₀, …, x_{n-1}` is `(1/n) ∑_{i<n} δ_{xᵢ}`. -/
theorem toMeasure_sampleEmpiricalMeasure (x : ℕ → X) {n : ℕ} (hn : n ≠ 0) :
    (sampleEmpiricalMeasure x n : Measure X) =
      (n : ℝ≥0∞)⁻¹ • ∑ i ∈ range n, Measure.dirac (x i) := by
  have : max n 1 = n := max_eq_left (Nat.one_le_iff_ne_zero.mpr hn)
  simp only [sampleEmpiricalMeasure, ProbabilityMeasure.coe_mk, this]

open scoped Classical in
/-- **Empirical frequency of a set.** For `n ≥ 1` and a measurable set `A`, the empirical measure
of `x₀, …, x_{n-1}` gives `A` the mass `#{i < n : xᵢ ∈ A} / n`. -/
theorem sampleEmpiricalMeasure_apply (x : ℕ → X) {n : ℕ} (hn : n ≠ 0) {A : Set X}
    (hA : MeasurableSet A) :
    (sampleEmpiricalMeasure x n : Measure X) A =
      (n : ℝ≥0∞)⁻¹ * ((range n).filter (fun i => x i ∈ A)).card := by
  rw [toMeasure_sampleEmpiricalMeasure x hn, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul]
  congr 1
  simp_rw [Measure.dirac_apply' _ hA]
  rw [Finset.sum_indicator_eq_sum_filter]
  simp

end MathlibExt.Probability.SampleEmpiricalMeasure
