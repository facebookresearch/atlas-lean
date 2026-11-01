/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Skyline
import Mathlib.Tactic.NormNum

/-!
# Tests for the classic skyline plot

The skyline model on its canonical product space (non-vacuity), the estimates' mean and
variance there, the interval maximizer at concrete values, and a junk value outside the
domain.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Skyline

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- Population sizes `θ k = k` (a growing population backwards in time). -/
def growing : ℕ → ℝ := fun k => k

lemma growing_pos : ∀ k ∈ Icc 2 5, 0 < growing k := fun k hk => by
  have : 2 ≤ k := (mem_Icc.mp hk).1
  simp only [growing]
  exact_mod_cast (by omega : 0 < k)

/-- A concrete skyline model for five genes (non-vacuity of `SkylineTimes`). -/
noncomputable def model : SkylineTimes (skylinePiMeasure 5 growing growing_pos) 5 growing :=
  SkylineTimes.ofPi 5 growing_pos

/-- In that model the skyline estimate for three lineages has mean `3` and variance `9`. -/
example : (skylinePiMeasure 5 growing growing_pos)[fun ω =>
      skylineEstimate 3 (model.T 3 ω)] = 3 ∧
    Var[fun ω => skylineEstimate 3 (model.T 3 ω); skylinePiMeasure 5 growing growing_pos] = 9 := by
  refine ⟨?_, ?_⟩
  · rw [model.integral_skylineEstimate (by decide)]
    norm_num [growing]
  · rw [model.variance_skylineEstimate (by decide)]
    norm_num [growing]

/-- With three pairs and an interval of length `2`, `θ = 6` beats `θ = 1`. -/
example : skylineLogLik 3 2 1 ≤ skylineLogLik 3 2 (3 * 2) :=
  skylineLogLik_le (by norm_num) (by norm_num) (by norm_num)

/-- `θ = 1` is not the maximizer for `c = 3`, `w = 2`. -/
example : skylineLogLik 3 2 1 ≠ skylineLogLik 3 2 (3 * 2) := by
  rw [Ne, skylineLogLik_eq_iff (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Junk value outside the domain: at `θ = 0` Lean's `x / 0 = 0` and `log 0 = 0` give
`ℓ = 0`. -/
example : skylineLogLik 3 2 0 = 0 := by
  simp [skylineLogLik]

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Skyline
