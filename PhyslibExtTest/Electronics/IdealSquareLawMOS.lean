/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.IdealSquareLawMOS
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.IdealSquareLawMOS

namespace PhyslibExtTest.Electronics.IdealSquareLawMOS

/-- Triode region at concrete values: `beta = 2`, `u = 3`, `Vds = 1`
gives `2 * (3 * 1 - 1 / 2) = 5`. -/
example : current 2 3 1 = 5 := by
  rw [current_of_triode 2 3 1 (by norm_num) (by norm_num) (by norm_num)]
  norm_num [triodeCurrent]

/-- Saturation at concrete values: `beta = 2`, `u = 3`, `Vds = 5`
gives `2 * 3^2 / 2 = 9`. -/
example : current 2 3 5 = 9 := by
  rw [current_of_saturation 2 3 5 (by norm_num) (by norm_num)]
  norm_num [saturationCurrent]

/-- Cutoff: nonpositive overdrive gives zero current. -/
example : current 2 (-1) 5 = 0 :=
  current_of_nonpos 2 (-1) 5 (by norm_num)

/-- At the boundary `Vds = u = 3` both active formulas give `9`. -/
example : current 2 3 3 = 9 := by
  rw [(current_at_boundary 2 3 (by norm_num)).1]
  norm_num [triodeCurrent]

example : triodeCurrent 2 3 3 = saturationCurrent 2 3 :=
  triode_eq_saturation_at_boundary 2 3

/-- Transconductance in the triode region: at `beta = 2`, `Vds = 1`,
`gm = beta * Vds = 2`. -/
example : HasDerivAt (fun u' : ℝ => current 2 u' 1) 2 3 := by
  simpa using hasDerivAt_u_triode 2 3 1 (by norm_num) (by norm_num)

/-- Output conductance in saturation is zero: at `beta = 2`, `u = 3`,
`Vds = 5`, `gds = 0`. -/
example : HasDerivAt (fun V : ℝ => current 2 3 V) 0 5 :=
  hasDerivAt_vds_saturation 2 3 5 (by norm_num) (by norm_num)

/-- The bundled contract at a concrete device constant. -/
example : (∀ u Vds : ℝ, 0 ≤ Vds → u ≤ 0 → current 2 u Vds = 0)
    ∧ (∀ u Vds : ℝ, 0 ≤ Vds → 0 ≤ current 2 u Vds) := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, h15⟩ :=
    idealSquareLawMOS_spec 2 (by norm_num)
  exact ⟨h1, h15⟩

end PhyslibExtTest.Electronics.IdealSquareLawMOS
