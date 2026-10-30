/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher

/-! Tests for the Wright–Fisher diffusion ODE facts: boundary values, neutral case, explicit
instances of the generator identities, uniqueness, Wright's density and the binomial step. -/

open Real Set

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.WrightFisher

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-! ### Kimura's fixation probability -/

example : kimuraFixation 3 0 = 0 := kimuraFixation_zero_right 3

example : kimuraFixation (-5) 1 = 1 := kimuraFixation_one_right (-5)

example : kimuraFixation 0 (1 / 3) = 1 / 3 := kimuraFixation_neutral _

example : kimuraFixation 1 (1 / 2) = (1 - exp (-1)) / (1 - exp (-2)) := by
  norm_num [kimuraFixation]

example (x : ℝ) : generator 7 (kimuraFixation 7) x = 0 := generator_kimuraFixation 7 x

example (x : ℝ) : generator 0 (kimuraFixation 0) x = 0 := generator_kimuraFixation 0 x

/-- Deleterious alleles still have a fixation probability in `[0, 1]`. -/
example : kimuraFixation (-2) (1 / 4) ∈ Icc (0 : ℝ) 1 :=
  kimuraFixation_mem_Icc (-2) ⟨by norm_num, by norm_num⟩

example : (1 / 2 : ℝ) < kimuraFixation 1 (1 / 2) :=
  lt_kimuraFixation one_pos ⟨by norm_num, by norm_num⟩

/-- Uniqueness, neutral case: any admissible solution with `u 0 = 0`, `u 1 = 1` is the identity. -/
example (u : ℝ → ℝ) (hc : ContinuousOn u (Icc 0 1)) (hu : ContDiffOn ℝ 2 u (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, generator 0 u x = 0) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    u (1 / 2) = 1 / 2 := by
  rw [eq_kimuraFixation_of_contDiffOn hc hu hgen h0 h1 (1 / 2) ⟨by norm_num, by norm_num⟩,
    kimuraFixation_neutral]

/-- Uniqueness with selection: Kimura's formula itself is recovered at `σ = 1`. -/
example (u : ℝ → ℝ) (hc : ContinuousOn u (Icc 0 1)) (hd : DifferentiableOn ℝ u (Ioo 0 1))
    (hd' : DifferentiableOn ℝ (deriv u) (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, generator 1 u x = 0) (h0 : u 0 = 0) (h1 : u 1 = 1) :
    u (1 / 2) = (1 - exp (-1)) / (1 - exp (-2)) := by
  rw [eq_kimuraFixation_of_generator_eq_zero hc hd hd' hgen h0 h1 (1 / 2)
    ⟨by norm_num, by norm_num⟩]
  norm_num [kimuraFixation]

/-! ### Mean absorption time, heterozygosity, moments -/

example : meanAbsorptionTime 0 = 0 := meanAbsorptionTime_zero

example : meanAbsorptionTime 1 = 0 := meanAbsorptionTime_one

/-- Starting from `x = 1/2`, the mean absorption time is `2 log 2` (i.e. `≈ 2.77 N` generations). -/
example : meanAbsorptionTime (1 / 2) = 2 * log 2 := by
  simp only [meanAbsorptionTime]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, log_inv]
  ring

example : generator 0 meanAbsorptionTime (1 / 2) = -1 :=
  generator_meanAbsorptionTime ⟨by norm_num, by norm_num⟩

example : generator 0 (fun y => 2 * y * (1 - y)) (1 / 2) = -(1 / 2) := by
  rw [generator_heterozygosity]
  norm_num

example (x : ℝ) : generator 0 (fun y => y ^ 2) x = x - x ^ 2 := by
  rw [generator_pow]
  norm_num

example (x : ℝ) : generator 0 (fun y => y ^ 3) x = 3 * (x ^ 2 - x ^ 3) := by
  rw [generator_pow]
  norm_num [Nat.choose]

example (x : ℝ) : generator 0 (fun y => y ^ 1) x = 0 := by
  rw [generator_pow]
  norm_num

/-! ### Wright's stationary density -/

/-- With `α = β = 1/2` Wright's density is uniform. -/
example (x : ℝ) : wrightDensity (1 / 2) (1 / 2) x = 1 := by
  norm_num [wrightDensity]

example : deriv (fun y => y * (1 - y) * wrightDensity 1 2 y) (1 / 3) =
    2 * (1 * (1 - 1 / 3) - 2 * (1 / 3)) * wrightDensity 1 2 (1 / 3) :=
  deriv_flux_wrightDensity 1 2 ⟨by norm_num, by norm_num⟩

example : ∫ x in (0 : ℝ)..1, wrightDensity (1 / 2) (1 / 2) x = 1 := by
  rw [integral_wrightDensity (by norm_num) (by norm_num)]
  norm_num

/-! ### One Wright–Fisher generation -/

/-- With a single gene copy, heterozygosity is lost in one generation. -/
example (x : unitInterval) :
    ∫ k, 2 * ((k : ℝ) / 1) * (1 - (k : ℝ) / 1) ∂(ProbabilityTheory.binomial 1 x) = 0 := by
  have h := integral_binomial_heterozygosity 1 one_ne_zero x
  norm_num at h ⊢
  exact h

example (x : unitInterval) :
    ∫ k, 2 * ((k : ℝ) / 4) * (1 - (k : ℝ) / 4) ∂(ProbabilityTheory.binomial 4 x) =
      3 / 4 * (2 * x * (1 - x)) := by
  have h := integral_binomial_heterozygosity 4 (by norm_num) x
  norm_num at h ⊢
  rw [h]

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.WrightFisher
