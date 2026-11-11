/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.Sojourn

/-! Tests for the neutral Green's function: values on both branches, the boundary cases
`p = 0, 1`, the Green's representation, and the mean absorption time from `p = 1/2`. -/

open Real Set

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.Sojourn

open MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Below the starting frequency: `G(1/2, 1/4) = 2 (1/2) / (3/4) = 4/3`. -/
example : neutralGreen (1 / 2) (1 / 4) = 4 / 3 := by norm_num [neutralGreen]

/-- Above the starting frequency: `G(1/2, 3/4) = 2 (1/2) / (3/4) = 4/3` (symmetry about `1/2`). -/
example : neutralGreen (1 / 2) (3 / 4) = 4 / 3 := by norm_num [neutralGreen]

/-- On the diagonal both branches give `2`. -/
example (p : ℝ) (hp : p ≠ 1) : neutralGreen p p = 2 := by
  have : 1 - p ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  simp [neutralGreen, this]

/-- An absent allele (`p = 0`) spends no time in the interior. -/
example (g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, neutralGreen 0 x * g x = 0 :=
  integral_neutralGreen_left g

example (g : ℝ → ℝ) : ∫ x in (0 : ℝ)..1, neutralGreen 1 x * g x = 0 :=
  integral_neutralGreen_right g

/-- Green's representation with `g = 1`: `u(p) = ∫ G(p, x) dx` solves `L_0 u = -1`. -/
example : generator 0 (fun q => ∫ x in (0 : ℝ)..1, neutralGreen q x * 1) (1 / 3) = -1 := by
  exact generator_integral_neutralGreen (g := fun _ => 1) continuous_const (p := 1 / 3)
    ⟨by norm_num, by norm_num⟩

/-- Starting from `p = 1/2`, the expected absorption time is `2 log 2` (units of `2N`
generations), i.e. `≈ 2.77 N` generations. -/
example : ∫ x in (0 : ℝ)..1, neutralGreen (1 / 2) x = 2 * log 2 := by
  rw [integral_neutralGreen ⟨by norm_num, by norm_num⟩, meanAbsorptionTime]
  norm_num
  rw [one_div, log_inv]
  ring

/-- Boundary cases of the sojourn integral. -/
example : ∫ x in (0 : ℝ)..1, neutralGreen 0 x = 0 := by
  simpa using integral_neutralGreen (p := 0) ⟨le_rfl, zero_le_one⟩

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.Sojourn
