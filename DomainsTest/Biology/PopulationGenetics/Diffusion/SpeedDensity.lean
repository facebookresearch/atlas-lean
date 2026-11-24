/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Diffusion.SpeedDensity

/-! Tests for speed density and the canonical form: generic restatements and
the neutral specializations. -/

open Real Set MeasureTheory
open MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SpeedDensity

example {b a : ℝ → ℝ} (h : IsRegularDiffusion b a) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < speedDensity b a x :=
  speedDensity_pos_of_isRegular h hx

example {b a : ℝ → ℝ} (h : IsRegularDiffusion b a) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ (deriv f) (Ioo 0 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    diffusionGenerator b a f x =
      (1 / speedDensity b a x) * deriv (fun y => deriv f y / scaleDensity b a y) x :=
  diffusionGenerator_eq_one_div_speedDensity h hf' hx

example {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    speedDensity (fun _ => 0) (fun x => x * (1 - x)) x = 2 / (x * (1 - x)) :=
  speedDensity_neutral x

example {θ₁ θ₂ : ℝ} (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) :
    ∫ x in (0 : ℝ)..1, mutationSpeedDensity θ₁ θ₂ x =
      2 * ProbabilityTheory.beta θ₁ θ₂ :=
  integral_mutationSpeedDensity hθ₁ hθ₂

example (b a : ℝ → ℝ) : speedMeasure b a =
    (volume.restrict (Ioo 0 1)).withDensity
      (fun x => ENNReal.ofReal (speedDensity b a x)) := rfl

/-- Total mass for `b = 0`, `a = 1` (speed density `2` on `(0, 1)`): the
speed measure has mass `2`, not infinite mass from outside the state space. -/
example : speedMeasure (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) Set.univ = 2 := by
  have hψ : ∀ x, scaleDensity (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) x = 1 := fun x => by
    simp [scaleDensity]
  simp [speedMeasure, speedDensity, hψ]

-- Neutral case through the mutation formulas: `α = θ₁ = θ₂ = 0` gives `m = 2/(x(1-x))`.
example {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    selectionMutationSpeedDensity 0 0 0 x = 2 / (x * (1 - x)) := by
  rw [selectionMutationSpeedDensity_eq hx]
  simp [selectionMutationScaleDensity, mutationScaleDensity]

-- The unnormalized mutation speed is twice Wright's density at half parameters.
example (θ₁ θ₂ x : ℝ) :
    mutationSpeedDensity θ₁ θ₂ x = 2 * wrightDensity (θ₁ / 2) (θ₂ / 2) x := by
  change 2 * x ^ (θ₁ - 1) * (1 - x) ^ (θ₂ - 1) =
    2 * (x ^ (2 * (θ₁ / 2) - 1) * (1 - x) ^ (2 * (θ₂ / 2) - 1))
  rw [show 2 * (θ₁ / 2) - 1 = θ₁ - 1 from by ring, show 2 * (θ₂ / 2) - 1 = θ₂ - 1 from by ring]
  ring

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SpeedDensity
