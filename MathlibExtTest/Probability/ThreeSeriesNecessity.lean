/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ThreeSeriesNecessity

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open MathlibExt.Probability.ThreeSeriesNecessity
open ProbabilityTheory.KolmogorovThreeSeries

namespace MathlibExtTest.Probability.ThreeSeriesNecessity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Truncation at level 2 kills `3`. -/
theorem truncationRV_two_three : truncatedRV (fun (_ : ℕ) (_ : Unit) => (3 : ℝ)) 2 0 () = 0 := by
  rw [truncatedRV_apply]
  show (if |(3 : ℝ)| ≤ 2 then (3 : ℝ) else 0) = 0
  rw [ite_eq_right (by norm_num)]

/-- Truncation at level 2 fixes `1`. -/
theorem truncationRV_two_one : truncatedRV (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) 2 0 () = 1 := by
  rw [truncatedRV_apply]
  show (if |(1 : ℝ)| ≤ 2 then (1 : ℝ) else 0) = 1
  rw [ite_eq_left (by norm_num)]

/-- Signature restatement: the truncation of a measurable random variable
is measurable. -/
theorem measurable_truncationRV_test {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (A : ℝ)
    (n : ℕ) : Measurable (truncatedRV X A n) :=
  measurable_truncatedRV hX A n

/-- Signature restatement: truncation preserves independence. -/
theorem iIndepFun_truncationRV_test {X : ℕ → Ω → ℝ} (hX : iIndepFun X μ) (A : ℝ) :
    iIndepFun (fun n => truncatedRV X A n) μ :=
  iIndepFun_truncatedRV hX A

omit [MeasurableSpace Ω] in
/-- Signature restatement: a truncation is bounded by `A` in absolute value. -/
theorem abs_truncationRV_le_test {X : ℕ → Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (ω : Ω) :
    |truncatedRV X A n ω| ≤ A :=
  abs_truncatedRV_le hA n ω

omit [MeasurableSpace Ω] in
/-- Signature restatement: truncation is the identity at points with
`|Xₙ| ≤ A`. -/
theorem truncationRV_eq_of_abs_le_test {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : |X n ω| ≤ A) : truncatedRV X A n ω = X n ω :=
  truncatedRV_eq_of_abs_le h

/-- The alternating-harmonic counterexample, revisited through the
assembly theorem: for the deterministic alternating family, the mean
partial sums of the truncations converge, the variances are summable
(they are all `0`), and yet the means themselves are not `Summable` —
so the corrected form of the necessity theorem is sharp. -/
theorem three_series_necessity_alternating :
    ∃ (X : ℕ → Unit → ℝ) (A : ℝ),
      (∃ L : ℝ, Tendsto (fun n => ∑ k ∈ Finset.range n,
        ∫ ω, truncatedRV X A k ω ∂(Measure.dirac ())) atTop (nhds L)) ∧
      Summable (fun n => variance (truncatedRV X A n) (Measure.dirac ())) ∧
      ¬ Summable (fun n => ∫ ω, truncatedRV X A n ω ∂(Measure.dirac ())) := by
  obtain ⟨X, A, hA, hmeas, hindep, htend, _htendTrunc, hnot⟩ :=
    summable_mean_necessity_false
  obtain ⟨hL, hSumm⟩ := three_series_necessity_mean_variance hmeas hindep hA htend
  exact ⟨X, A, hL, hSumm, hnot⟩

#print axioms three_series_necessity_mean_variance

#print axioms summable_mean_necessity_false

#print axioms three_series_necessity_alternating

/-- The canonical square-integral bound is available through a normal import. -/
example [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) {B : ℝ}
    (hsq : ∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ ≤ B) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt B) :=
  ProbabilityTheory.eLpNorm_one_le_sqrt_integral_sq hf hsq

end MathlibExtTest.Probability.ThreeSeriesNecessity
