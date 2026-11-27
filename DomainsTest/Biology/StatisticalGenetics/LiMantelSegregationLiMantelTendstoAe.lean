/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe
import Mathlib.Tactic.NormNum

/-!
# Tests for the Li–Mantel estimator consistency

The zero-truncated binomial law vanishes outside `1 ≤ k ≤ s`; the estimator is `0` for `n = 0`;
on three sibships with affected counts `2, 1, 0` and size `2` it equals `(3 - 1) / (6 - 1) = 2/5`;
and the centered estimator converges almost surely to `0`, a corollary of
`liMantel_tendsto_ae`.
-/

@[expose] public section

open WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted
open MeasureTheory ProbabilityTheory Filter Topology

namespace DomainsTest.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe

/-- The truncated law vanishes at `k = 0`: ascertained sibships have an affected child. -/
example (s : ℕ) (p : ℝ) : truncBinom s p 0 = 0 := by
  simp [truncBinom]

/-- The truncated law vanishes above the sibship size. -/
example (s : ℕ) (p : ℝ) (k : ℕ) (hk : s < k) : truncBinom s p k = 0 := by
  simp only [truncBinom]
  rw [ite_eq_right (by omega)]

/-- With no sibships the estimator is `0` (both sums are empty). -/
example (s : ℕ) (x : ℕ → ℕ) : liMantel s x 0 = 0 := by
  simp [liMantel, affectedCount, singletonCount]

/-- Affected counts `2, 1, 0` on three sibships. -/
private def x3 : ℕ → ℕ := fun i => if i = 0 then 2 else if i = 1 then 1 else 0

/-- The three sibships have `R = 3` affected children. -/
private lemma affectedCount_x3 : affectedCount x3 3 = 3 := by
  decide

/-- Of the three sibships, `J = 1` is a singleton. -/
private lemma singletonCount_x3 : singletonCount x3 3 = 1 := by
  decide

/-- On counts `2, 1, 0` with size `2`, the estimator is `(3 - 1) / (6 - 1) = 2 / 5`. -/
example : liMantel 2 x3 3 = 2 / 5 := by
  simp only [liMantel, affectedCount_x3, singletonCount_x3]
  norm_num

/-- The centered estimator converges almost surely to `0`. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (X : ℕ → Ω → ℕ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i k, μ.real (X i ⁻¹' {k}) = truncBinom s p k) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => liMantel s (fun i => X i ω) n - p) atTop (𝓝 0) := by
  filter_upwards [liMantel_tendsto_ae μ s hs p hp₀ hp₁ X hmeas hindep hlaw] with ω hω
  simpa using hω.sub_const p

end DomainsTest.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe
