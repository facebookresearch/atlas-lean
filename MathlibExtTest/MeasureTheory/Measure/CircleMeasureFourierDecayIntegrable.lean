/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Measure.CircleMeasureFourierDecayIntegrable
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntegrableOn

open Filter MeasureTheory Set
open scoped ENNReal Topology
open MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted

-- Conjugation restricts to the negative first Fourier mode on the circle.
example (μ : Measure ℂ) (hfinite : μ univ < ⊤)
    (hsphere : ∀ᵐ z ∂μ, z ∈ Metric.sphere (0 : ℂ) 1)
    (hpow : Tendsto (fun n : ℕ => ∫ z, z ^ n ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ∫ z, z ^ n * star z ∂μ) atTop (𝓝 0) := by
  let : IsFiniteMeasure μ := ⟨hfinite⟩
  apply tendsto_integral_pow_mul_of_tendsto_integral_pow μ hfinite hsphere hpow
  refine Integrable.of_bound continuous_star.aestronglyMeasurable 1 ?_
  filter_upwards [hsphere] with z hz
  have hz' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  rw [norm_star, hz']
