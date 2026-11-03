/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.GoldbeterKoshland

/-! Tests for Goldbeter–Koshland ultrasensitivity: concrete steady states, the response
coefficient at sample Michaelis constants, the junk value outside the domain, and the
Michaelis–Menten value `81`. -/

open Set

namespace MathlibExtTest.Biology.Dynamics.GoldbeterKoshland

open MathlibExt.Biology.Dynamics.GoldbeterKoshland

/-- **Non-vacuity witness.** With `V₁ = 3/2`, `V₂ = 1`, `K₁ = 1`, `K₂ = 1/2`, the fraction
`W = 1/2` satisfies the steady-state balance. -/
example : (3 / 2 : ℝ) * (1 - 1 / 2) / (1 + (1 - 1 / 2)) = 1 * (1 / 2) / (1 / 2 + 1 / 2) := by
  norm_num

/-- The same steady state through Eq. 8: `rateRatio 1 (1/2) (1/2) = 3/2`. -/
example : rateRatio 1 (1 / 2) (1 / 2) = 3 / 2 := by norm_num [rateRatio]

/-- The Goldbeter–Koshland function picks it out: `G(3/2, 1, 1/2) = 1/2`. -/
example : goldbeterKoshland (3 / 2) 1 (1 / 2) = 1 / 2 :=
  (eq_goldbeterKoshland (W := 1 / 2) (by norm_num) one_pos (by norm_num) ⟨by norm_num, by norm_num⟩
    (by norm_num [rateRatio])).symm

/-- Equal maximal rates and equal Michaelis constants give half modification (Eq. 9). -/
example : goldbeterKoshland 1 1 1 = 1 / 2 := by
  rw [goldbeterKoshland_one one_pos one_pos]; norm_num

/-- The steady state lies in `(0, 1)` for sample parameters. -/
example : goldbeterKoshland 10 (1 / 100) (1 / 100) ∈ Ioo 0 1 :=
  goldbeterKoshland_mem_Ioo (by norm_num) (by norm_num) (by norm_num)

/-- Response coefficient at `K₁ = K₂ = 1` (Eq. 10): `81 · 1.1² / 1.9² = 9801 / 361`. -/
example : responseCoefficient 1 1 = 9801 / 361 := by
  rw [responseCoefficient_eq (by norm_num) (by norm_num)]; norm_num

/-- Response coefficient with saturated enzymes, `K₁ = K₂ = 0.01`: `81 · 0.11² / 0.91²`. -/
example : responseCoefficient 0.01 0.01 = 9801 / 8281 := by
  rw [responseCoefficient_eq (by norm_num) (by norm_num)]; norm_num

/-- At `K₁ = K₂ = 0` (outside the domain `K > 0`) the formula gives exactly `1`. -/
example : responseCoefficient 0 0 = 1 := by
  rw [responseCoefficient_eq (by norm_num) (by norm_num)]; norm_num

/-- Bounds `1 < R_v < 81` at sample constants. -/
example : 1 < responseCoefficient 0.01 0.01 ∧ responseCoefficient 0.01 0.01 < 81 :=
  ⟨one_lt_responseCoefficient (by norm_num) (by norm_num),
    responseCoefficient_lt_81 (by norm_num) (by norm_num)⟩

/-- Junk value outside the domain: at `W = 1` Lean's `a / 0 = 0` makes `rateRatio` vanish. -/
example (K₁ K₂ : ℝ) : rateRatio K₁ K₂ 1 = 0 := by simp [rateRatio]

/-- Michaelis–Menten response with `K = 1`: `S = 9` gives 90%, `S = 1/9` gives 10%, and the
ratio is `81`. -/
example : (9 : ℝ) / (1 / 9) = 81 :=
  michaelisMenten_ratio_eq one_pos (by norm_num) (by norm_num) (by norm_num [hill])
    (by norm_num [hill])

end MathlibExtTest.Biology.Dynamics.GoldbeterKoshland
