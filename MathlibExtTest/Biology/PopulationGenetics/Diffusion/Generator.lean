/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Generator
public import MathlibExt.Biology.PopulationGenetics.Diffusion.GeneralDiffusion

/-!
# Tests for the Wright–Fisher generator with selection and two-way mutation

The endpoint drifts are `θ₁ / 2` at `0` and `-θ₂ / 2` at `1`. At `α = θ₁ = 1`, `θ₂ = 0`,
`x = 1/2`, selection and mutation each contribute `1/4`.
-/

@[expose] public section

open Real Set Filter MathlibExt.Biology.PopulationGenetics.Diffusion
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.Generator

-- Bridge to the general one-dimensional diffusion generator.
example (α θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    selectionMutationGenerator α θ₁ θ₂ f x =
      diffusionGenerator (fun y => α * y * (1 - y) + (θ₁ * (1 - y) - θ₂ * y) / 2)
        (fun y => y * (1 - y)) f x := by
  simp only [selectionMutationGenerator, diffusionGenerator]

-- Kimura's fixation probability is harmonic for the mutation-free combined generator,
-- via the bridge to the selection generator.
example (α x : ℝ) : selectionMutationGenerator α 0 0 (kimuraFixation α) x = 0 := by
  rw [selectionMutationGenerator_zero_zero]
  exact generator_kimuraFixation α x

-- Neutral uniqueness for the combined generator, via the same bridge: the only solution
-- at `α = 0` is the identity on `[0, 1]`.
example {u : ℝ → ℝ} (hcont : ContinuousOn u (Icc 0 1)) (hu : ContDiffOn ℝ 2 u (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, selectionMutationGenerator 0 0 0 u x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) : ∀ x ∈ Icc (0 : ℝ) 1, u x = x := fun x hx => by
  have hgen' : ∀ x ∈ Ioo (0 : ℝ) 1, generator 0 u x = 0 := fun x hx => by
    rw [← selectionMutationGenerator_zero_zero]; exact hgen x hx
  rw [eq_kimuraFixation_of_contDiffOn hcont hu hgen' h0 h1 x hx, kimuraFixation_neutral]

-- Endpoints of `[0, 1]`: selection vanishes at both boundaries.
example (α θ₁ θ₂ : ℝ) : selectionMutationGenerator α θ₁ θ₂ id 0 = θ₁ / 2 := by
  rw [selectionMutationGenerator_id]; ring

example (α θ₁ θ₂ : ℝ) : selectionMutationGenerator α θ₁ θ₂ id 1 = -θ₂ / 2 := by
  rw [selectionMutationGenerator_id]; ring

-- Non-vacuity: selection and mutation both contribute at `x = 1/2`.
example : selectionMutationGenerator 1 1 0 id (1 / 2) = 1 / 2 := by
  rw [selectionMutationGenerator_id]; norm_num

-- The heterozygosity identity of the mutation generator is recovered at `α = 0`.
example (θ₁ θ₂ x : ℝ) :
    selectionMutationGenerator 0 θ₁ θ₂ (fun y => 2 * y * (1 - y)) x =
      -(2 * x * (1 - x)) + (θ₁ * (1 - x) - θ₂ * x) * (1 - 2 * x) := by
  rw [selectionMutationGenerator_zero_left, mutationGenerator_heterozygosity]

#print axioms selectionMutationGenerator_zero_zero
#print axioms selectionMutationGenerator_zero_left
#print axioms selectionMutationGenerator_neutral
#print axioms selectionMutationGenerator_eq
#print axioms selectionMutationGenerator_id
#print axioms selectionMutationGenerator_neutral_sq

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.Generator
