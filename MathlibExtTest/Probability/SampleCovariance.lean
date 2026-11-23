/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.SampleCovariance

/-!
# Tests for the unbiasedness of the sample covariance

Closed checks: `sampleCov_entry` gives the `N = 2` scalar sample variance `(x₁ - x₂)² / 2`, and
`sampleCov_expectation` applies to deterministic samples, whose hypotheses all hold with
covariance `0`, so their expected sample covariance vanishes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Statistics.PCA (sampleCov)

namespace MathlibExt.Probability.SampleCovariance

/-- `N = 2` scalar samples: the sample variance is `(x₁ - x₂)² / 2`. -/
example {Ω : Type*} (X : Fin 2 → Ω → (Fin 1 → ℝ)) (ω : Ω) :
    sampleCov (Matrix.of fun i j' => X i ω j') 0 0 = (X 0 ω 0 - X 1 ω 0) ^ 2 / 2 := by
  rw [sampleCov_entry]
  simp only [Fin.sum_univ_two]
  norm_num
  ring

/-- Deterministic samples satisfy every hypothesis of `sampleCov_expectation` with covariance
`0`, so the expected sample covariance vanishes. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : Fin 2 → ℝ) (j k : Fin 2) :
    ∫ _ω, sampleCov (Matrix.of fun (_ : Fin 3) j' => c j') j k ∂μ = 0 := by
  have h := sampleCov_expectation (N := 3) (d := 2) (μ := μ) (X := fun _ _ => c) (m := c)
    (Sig := 0) (by norm_num)
    (fun _ j => by simp)
    (fun _ j k => by rw [Matrix.zero_apply]; exact covariance_const_left (c j))
    (fun _ _ _ => indepFun_const_left c (fun _ => c))
    (fun _ _ => integrable_const _)
    (fun _ _ _ => integrable_const _) j k
  simpa using h

#print axioms sampleCov_expectation

end MathlibExt.Probability.SampleCovariance
