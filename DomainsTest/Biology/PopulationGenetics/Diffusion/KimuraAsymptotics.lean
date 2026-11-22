/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.KimuraAsymptotics
public import Mathlib.Tactic.NormNum

@[expose] public section

open Filter Topology
open MathlibExt.Biology.PopulationGenetics.Diffusion

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraAsymptotics

/-- Closed form at a nonzero scaled selection coefficient. -/
example :
    kimuraFixation 1 (1 / 2) =
      (1 - Real.exp (-1)) / (1 - Real.exp (-2)) := by
  rw [kimuraFixation_eq_of_ne_zero]
  · norm_num
  · norm_num

/-- The slope constant at neutrality is the continuous-extension value `1`. -/
example : kimuraSlope 0 = 1 := by simp [kimuraSlope]

/-- At `α = 0`, the fixed-`α` new-mutant limit is `1`. -/
example :
    Tendsto (fun M : ℕ => (M : ℝ) * kimuraFixation 0 (1 / (M : ℝ))) atTop
      (𝓝 1) := by
  simpa [kimuraSlope] using tendsto_natCast_mul_kimuraFixation_one_div 0

/-- For fixed `s = 1/2`, the diffusion limit is `1 - e^{-1}`, strictly below
Haldane's expression `2s = 1`. -/
example : 1 - Real.exp (-1 : ℝ) < 1 := by
  have h := (tendsto_kimuraFixation_natCast_mul_one_div (s := 1 / 2)
    (by norm_num)).2
  norm_num at h ⊢
  exact h

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraAsymptotics
