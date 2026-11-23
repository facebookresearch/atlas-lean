/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianL2Limit
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Tests for `L²` limits of Gaussian laws

Instances of the closure theorems on constant sequences (a real Gaussian variable, the vector of
Brownian values, a pre-Brownian motion as a Gaussian process), and the pairing theorem used to
pass means to the limit (`E[1 · X n] → E[1 · Y]`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathlibExtTest.Probability.Distributions.GaussianL2Limit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A constant sequence of real Gaussian variables: the limit theorem applies. -/
example {Y : Ω → ℝ} (hY : HasGaussianLaw Y P) : HasGaussianLaw Y P :=
  HasGaussianLaw.of_tendsto_eLpNorm_real (X := fun _ ↦ Y) (fun _ ↦ hY)
    hY.aemeasurable.aestronglyMeasurable (by simp)

/-- The vector case on `ℝ × ℝ`: a pair of Brownian values. -/
example {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    HasGaussianLaw (fun ω ↦ (B 1 ω, B 2 ω)) P :=
  HasGaussianLaw.of_tendsto_eLpNorm (X := fun _ ω ↦ (B 1 ω, B 2 ω))
    (fun _ ↦ hB.isGaussianProcess.hasGaussianLaw_prodMk)
    hB.isGaussianProcess.hasGaussianLaw_prodMk.aemeasurable.aestronglyMeasurable (by simp)

/-- The process case: a pre-Brownian motion as the limit of the constant sequence. -/
example {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) : IsGaussianProcess B P :=
  IsGaussianProcess.of_tendsto_eLpNorm (X := fun _ ↦ B) (fun _ ↦ hB.isGaussianProcess)
    (fun t ↦ (hB.aemeasurable t).aestronglyMeasurable) (by simp)

/-- Means pass to `L²` limits: the pairing with the constant `1`. -/
example [IsFiniteMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (h : Tendsto (fun n ↦ eLpNorm (X n - Y) 2 P) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
  simpa using tendsto_integral_mul_of_tendsto_eLpNorm (X := fun _ _ ↦ (1 : ℝ)) (Y := fun _ ↦ 1)
    (fun _ ↦ memLp_const 1) hX (memLp_const 1) hY (by simp) h

end MathlibExtTest.Probability.Distributions.GaussianL2Limit
