/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.CovarianceBandingRate

open Filter Topology Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.Norms.L2Operator
open MathlibExt.Probability.Statistics
open CovarianceBanding CovarianceBandingWanted

namespace MathlibExtTest.Probability.Statistics.CovarianceBandingRate

private lemma identity_mem : (1 : Matrix (Fin 2) (Fin 2) ℝ) ∈ bandableClass 1 1 1 := by
  refine ⟨Matrix.transpose_one, fun x => by simp, fun k hk j => ?_⟩
  have hempty : (Finset.univ.filter (fun i : Fin 2 => k < ((i : ℤ) - j).natAbs)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    omega
  rw [hempty, Finset.sum_empty]
  positivity

private noncomputable def estimator {n : ℕ} (X : Fin n → EuclideanSpace ℝ (Fin 2)) :=
  let Y := PCA.center (Matrix.of fun i j => X i j)
  band ⌈(Real.log 2 / n) ^ (-1 / 4 : ℝ)⌉₊ ((n : ℝ)⁻¹ • (Yᵀ * Y))

-- At the smallest allowed dimension, a single K and N work for both errors at exponent 1/4.
example {η : ℝ} (hη : 0 < η) : ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N,
    let μ := Measure.pi fun _ : Fin n => multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 1
    let threshold := K * (Real.log 2 / n) ^ (1 / 4 : ℝ)
    μ {X | threshold < ‖estimator X - 1‖} ≤ ENNReal.ofReal η ∧
      μ {X | threshold < ‖(estimator X)⁻¹ - 1‖} ≤ ENNReal.ofReal η := by
  have hlog : Tendsto (fun n : ℕ => Real.log ((2 : ℕ) : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨K, N, h⟩ := banded_sampleCovariance_rate (fun _ => 2) (fun _ => le_rfl) hlog
    (ε₀ := 1) (α := 1) (C := 1) zero_lt_one zero_lt_one zero_lt_one η hη
  refine ⟨K, N, fun n hn => ?_⟩
  simpa [estimator, show (2 : ℝ) * (1 + 1) = 4 by norm_num] using h n hn 1 identity_mem

end MathlibExtTest.Probability.Statistics.CovarianceBandingRate
