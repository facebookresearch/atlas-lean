/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179LittleO

/-!
# Tests for the subquadratic progression threshold

Check the normalized limit and two four-element sets with the same three-term count.
-/

namespace MathlibExtTest.Combinatorics.ManyThreeTermProgressionsErdosProblem179LittleO

open MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted
open Filter Topology

example : Tendsto (fun N : ℕ => (apThreshold 3 4 N : ℝ) / (N : ℝ) ^ 2) atTop (𝓝 0) :=
  Asymptotics.IsLittleO.tendsto_div_nhds_zero threeAPThresholdForFourAPLittleO_holds

example : apCount {10, 13, 16, 19} 3 = 2 ∧ HasAP {10, 13, 16, 19} 4 := by
  exact ⟨by decide, 10, 3, by decide, by decide⟩

example : apCount {10, 13, 16, 22} 3 = 2 ∧ ¬ HasAP {10, 13, 16, 22} 4 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨a, d, hd, h⟩
  have h₀ := h 0 (by decide)
  have h₁ := h 1 (by decide)
  have h₂ := h 2 (by decide)
  have h₃ := h 3 (by decide)
  simp at h₀ h₁ h₂ h₃
  omega

end MathlibExtTest.Combinatorics.ManyThreeTermProgressionsErdosProblem179LittleO
