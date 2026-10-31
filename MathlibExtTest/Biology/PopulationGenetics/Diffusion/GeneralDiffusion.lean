/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.GeneralDiffusion

/-! Tests for the selection duality, general one-dimensional diffusions and conditional
fixation times: concrete values, the junk values outside the parameter domains, non-vacuity
witnesses for `IsRegularDiffusion`, and the special cases (neutral, genic, `h = 1/2`). -/

open Real Set Filter
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.GeneralDiffusion

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-! ### Selection duality -/

/-- Two lines: `L_σ[(1 - x)^2] = x (1 - x) - 2σ x (1 - x)^2`. -/
example (σ x : ℝ) :
    generator σ (fun y => (1 - y) ^ 2) x = x * (1 - x) - 2 * σ * x * (1 - x) ^ 2 := by
  rw [generator_one_sub_pow]
  norm_num
  ring

/-- No lines: the constant `1` is annihilated. -/
example (σ x : ℝ) : generator σ (fun y => (1 - y) ^ 0) x = 0 := by
  rw [generator_one_sub_pow]
  simp

/-- The neutral case of the duality is the moment duality with Kingman's coalescent. -/
example (n : ℕ) (x : ℝ) :
    asgGenerator 0 (fun k => (1 - x) ^ k) n =
      (n.choose 2 : ℝ) * ((1 - x) ^ (n - 1) - (1 - x) ^ n) := by
  simp [asgGenerator]

/-- The stationary law puts no mass on `0` lines. -/
example (σ : ℝ) : asgStationary σ 0 = 0 := by simp [asgStationary]

/-- `π_1 = 2σ / (e^{2σ} - 1)`. -/
example (σ : ℝ) : asgStationary σ 1 = 2 * σ / (exp (2 * σ) - 1) := by
  simp [asgStationary]

/-- Junk value outside the domain: for `σ = 0` every weight is `0` (no stationary law). -/
example (k : ℕ) : asgStationary 0 k = 0 := by simp [asgStationary]

/-- Detailed balance between one and two lines: `π_1 σ = π_2`. -/
example (σ : ℝ) : asgStationary σ 1 * σ = asgStationary σ 2 := by
  simpa using asgStationary_detailed_balance σ 1

/-- For `σ = 1` the weights sum to `1` and the generating function at `1 - x` is the loss
probability. -/
example : HasSum (asgStationary 1) 1 := hasSum_asgStationary one_pos

example (x : ℝ) :
    HasSum (fun k => asgStationary 1 k * (1 - x) ^ k) (1 - kimuraFixation 1 x) :=
  hasSum_asgStationary_mul_one_sub_pow one_pos x

/-! ### General diffusions -/

/-- Non-vacuity witness: genic selection with `σ = 1` is a regular diffusion. -/
example : IsRegularDiffusion (fun x => 1 * x * (1 - x)) (fun x => x * (1 - x)) :=
  isRegularDiffusion_wrightFisher 1

/-- Non-vacuity witness: dominance with `c = 1`, `h = 0` (a recessive allele). -/
example : IsRegularDiffusion (dominanceDrift 1 0) (fun x => x * (1 - x)) :=
  isRegularDiffusion_dominance 1 0

/-- Non-vacuity witness: Brownian motion with drift (`a = 1`, `b = μ`). -/
example (μ : ℝ) : IsRegularDiffusion (fun _ => μ) (fun _ => 1) where
  pos _ _ := one_pos
  continuousOn := continuousOn_const
  continuousOn_div := continuousOn_const
  intervalIntegrable_div := intervalIntegrable_const

/-- Brownian motion without drift: scale density `1`, fixation probability `p`. -/
example (p : ℝ) : fixationProb (fun _ => 0) (fun _ => 1) p = p := by
  simp [fixationProb, scaleFunction, scaleDensity]

/-- Neutral Wright–Fisher: the fixation probability is the initial frequency. -/
example : fixationProb (fun x => 0 * x * (1 - x)) (fun x => x * (1 - x)) (1 / 3) = 1 / 3 := by
  rw [fixationProb_wrightFisher 0 ⟨by norm_num, by norm_num⟩, kimuraFixation_neutral]

/-- Genic selection: the general formula is Kimura's. -/
example (σ : ℝ) :
    fixationProb (fun x => σ * x * (1 - x)) (fun x => x * (1 - x)) (1 / 2) =
      kimuraFixation σ (1 / 2) :=
  fixationProb_wrightFisher σ ⟨by norm_num, by norm_num⟩

/-- Boundary values of the fixation probability. -/
example : fixationProb (dominanceDrift 1 0) (fun x => x * (1 - x)) 0 = 0 :=
  fixationProb_zero _ _

example : fixationProb (dominanceDrift 1 0) (fun x => x * (1 - x)) 1 = 1 :=
  (isRegularDiffusion_dominance 1 0).fixationProb_one

/-- Dominance with `h = 1/2` is genic selection with `σ = c`. -/
example (c : ℝ) : dominanceDrift c (1 / 2) = fun x => c * x * (1 - x) := by
  funext x
  simp only [dominanceDrift]
  ring

example (c p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb (dominanceDrift c (1 / 2)) (fun x => x * (1 - x)) p = kimuraFixation c p := by
  have : dominanceDrift c (1 / 2) = fun x => c * x * (1 - x) := by
    funext x
    simp only [dominanceDrift]
    ring
  rw [this, fixationProb_wrightFisher c hp]

/-- The general Green's function reproduces the neutral one: `G(1/2, 1/4) = 4/3`. -/
example : greenFunction (fun _ => 0) (fun x => x * (1 - x)) (1 / 2) (1 / 4) = 4 / 3 := by
  rw [greenFunction_neutral _ ⟨by norm_num, by norm_num⟩]
  norm_num [neutralGreen]

/-- The Green's representation is not vacuous: for Brownian motion on `(0, 1)` (`b = 0`,
`a = 1`) and `g = 1`, the Green integral solves `v''/2 = -1` at `1/2`. -/
example :
    diffusionGenerator (fun _ => 0) (fun _ => 1)
      (fun q => ∫ x in (0 : ℝ)..1, greenFunction (fun _ => 0) (fun _ => 1) q x * 1) (1 / 2) =
      -1 := by
  have hψ : ∀ y, scaleDensity (fun _ => 0) (fun _ => 1) y = 1 := fun y => by
    simp [scaleDensity]
  have hS : ∀ y, scaleFunction (fun _ => 0) (fun _ => 1) y = y := fun y => by
    simp [scaleFunction, hψ]
  have hreg : IsRegularDiffusion (fun _ => (0 : ℝ)) (fun _ => 1) :=
    ⟨fun _ _ => one_pos, continuousOn_const, continuousOn_const, intervalIntegrable_const⟩
  exact diffusionGenerator_integral_greenFunction (g := fun _ => 1) hreg continuousOn_const
    (fun q _ => by
      simp only [hS, hψ]
      exact (by fun_prop : Continuous fun x : ℝ => x * 1 / (1 * 1)).intervalIntegrable _ _)
    (fun q _ => by
      simp only [hS, hψ]
      exact (by fun_prop : Continuous fun x : ℝ => (1 - x) * 1 / (1 * 1)).intervalIntegrable _ _)
    ⟨by norm_num, by norm_num⟩

/-- Dirichlet conditions of the Green integral. -/
example (b a g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, greenFunction b a 0 x * g x = 0 :=
  integral_greenFunction_zero_left b a g

example (b a g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, greenFunction b a 1 x * g x = 0 :=
  integral_greenFunction_one_left b a g

/-! ### Conditional times -/

/-- From `p = 1/2`, the conditional fixation time is `2 log 2`, the same as the unconditional
absorption time (by symmetry). -/
example : neutralFixationTime (1 / 2) = 2 * log 2 := by
  rw [neutralFixationTime]
  norm_num
  rw [one_div, log_inv]
  ring

/-- Junk value: at `p = 0` the formula divides by `0` and gives `0`, not the limit `2`. -/
example : neutralFixationTime 0 = 0 := by simp [neutralFixationTime]

example : Tendsto neutralFixationTime (𝓝[>] 0) (𝓝 2) := tendsto_neutralFixationTime_zero

/-- Loss is fixation of the other allele. -/
example : neutralLossTime (1 / 4) = neutralFixationTime (3 / 4) := by
  rw [neutralLossTime_eq]
  norm_num

/-- Total expectation at `p = 1/2`. -/
example : (1 / 2) * neutralFixationTime (1 / 2) + (1 - 1 / 2) * neutralLossTime (1 / 2) =
    meanAbsorptionTime (1 / 2) :=
  mul_neutralFixationTime_add_mul_neutralLossTime ⟨by norm_num, by norm_num⟩

/-- The general conditional sojourn density integrates to the Kimura–Ohta time. -/
example :
    ∫ x in (0 : ℝ)..1, conditionalGreen (fun _ => 0) (fun x => x * (1 - x)) (1 / 2) x =
      2 * log 2 := by
  rw [integral_conditionalGreen_neutral ⟨by norm_num, by norm_num⟩, neutralFixationTime]
  norm_num
  rw [one_div, log_inv]
  ring

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.GeneralDiffusion
