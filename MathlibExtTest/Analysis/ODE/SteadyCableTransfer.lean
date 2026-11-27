/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.SteadyCableTransfer

/-! Cable parameters and initial data for steady transfer. -/

open Real Set

namespace MathlibExtTest.Biology.Biophysics.MembraneCable

open MathlibExt.Biology.Biophysics.MembraneCable

/-- `rm = 4`, `ri = 1`: `λ = 2` and `r∞ = 2`. -/
example : lengthConstant 4 1 = 2 ∧ charResistance 4 1 = 2 := by
  norm_num [lengthConstant, charResistance, Real.sqrt_eq_iff_eq_sq]

/-- `rm = 9`, `ri = 4`: `λ² = 9 / 4` and `r∞ = ri λ`. -/
example : lengthConstant 9 4 ^ 2 = 9 / 4 ∧ charResistance 9 4 = 4 * lengthConstant 9 4 :=
  ⟨lengthConstant_sq (by norm_num) (by norm_num), charResistance_eq (by norm_num) (by norm_num)⟩

/-- The transfer-form solution starts from the prescribed voltage and current. -/
example (V₀ I₀ : ℝ) : cableVoltage 4 1 V₀ I₀ 0 = V₀ ∧ cableCurrent 4 1 V₀ I₀ 0 = I₀ := by
  simp [cableVoltage, cableCurrent]

/-- Unit parameters and unit input current determine both transfer components one unit away. -/
example {V I : ℝ → ℝ} (h : IsSteadyState 1 1 (Icc 0 1) V I) (hV : V 0 = 0) (hI : I 0 = 1) :
    V 1 = -sinh 1 ∧ I 1 = cosh 1 := by
  simpa [hV, hI, cableVoltage, cableCurrent, lengthConstant, charResistance] using
    h.eq_cable_Icc one_pos one_pos (right_mem_Icc.mpr zero_le_one)

end MathlibExtTest.Biology.Biophysics.MembraneCable
