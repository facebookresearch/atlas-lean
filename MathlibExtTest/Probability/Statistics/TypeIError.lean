/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.TypeIError

/-!
# Tests for type-I error bounds

Concrete instances of `MathlibExt.Probability.Statistics.TypeIError` under the uniform law on
`[0, 1]`: the identity p-value at level `1 / 10`, and the critical-value rule with rejection set
`Iic (9 / 10)` at level `9 / 10`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.TypeIError

namespace MathlibExtTest.Probability.Statistics.TypeIError

/-- The identity p-value under the uniform law on `[0, 1]` rejects with type-I error at most
`1 / 10` at level `1 / 10`. -/
example :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).real {x : ℝ | x ≤ (1 / 10 : ℝ)} ≤ (1 / 10 : ℝ) := by
  have h := typeI_error_le_of_hasLaw_uniform_pValue (p := id) HasLaw.id
    (α := (1 / 10 : ℝ)) (by norm_num)
  simpa using h

/-- The critical-value rule rejecting when the statistic is at most `9 / 10` under the uniform
law on `[0, 1]` has type-I error at most `9 / 10` (calibrated set `Iic (9 / 10)`). -/
example :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) ((fun x : ℝ => x) ⁻¹' Set.Iic (9 / 10 : ℝ)) ≤
      ENNReal.ofReal (9 / 10) := by
  have hset : Set.Iic (9 / 10 : ℝ) ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) (9 / 10) := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2.1, hx.1⟩
    · intro hx
      exact ⟨hx.2, hx.1, by linarith [hx.2]⟩
  have hcal : (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Iic (9 / 10 : ℝ)) ≤
      ENNReal.ofReal (9 / 10) := by
    rw [Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero]
  exact typeI_error_le_of_hasLaw (T := fun x : ℝ => x) (R := Set.Iic (9 / 10 : ℝ))
    HasLaw.id measurableSet_Iic hcal

end MathlibExtTest.Probability.Statistics.TypeIError
