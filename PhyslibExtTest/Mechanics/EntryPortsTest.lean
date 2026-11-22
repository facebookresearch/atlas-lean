/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EntryPorts

import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Mechanics.EntryPorts`

SI units: `ρ0 = 1.225 kg/m³`, `H = 7000 m`, `β = 500 kg/m²`, `γ = π / 6` (`sin γ = 1 / 2`), a
declared band entered at `he = 40000 m` with `ve = 3000 m/s`; so `K = 17.15`.

* at `30000 m`, below the entry altitude, the density is positive and the speed lies strictly
  between `0` and the entry speed;
* the infinite-entry profile, which drops the `exp (-he / H)` term, misses the entry speed at
  the entry altitude.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.EntryPorts

open _root_.EntryPorts

-- Nonzero density and descent: at `30000 m`, below the entry altitude, the density is positive
-- and the speed lies strictly between `0` and the entry speed (about `2.51 km/s`).
example :
    0 < exponentialDensity 1.225 7000 30000 ∧
      0 < ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 30000 ∧
      ballisticVelocity 1.225 7000 500 (Real.pi / 6) 40000 3000 30000 < 3000 := by
  have hsinpos : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  have hK : 0 < ballisticK 1.225 7000 500 (Real.pi / 6) :=
    ballisticK_pos (by norm_num) (by norm_num) (by norm_num) hsinpos
  refine ⟨?_, ?_, ?_⟩
  · unfold exponentialDensity
    exact mul_pos (by norm_num) (Real.exp_pos _)
  · exact ballisticVelocity_pos (by norm_num) _ _ _ _ _ _
  · have harg : (-40000 : ℝ) / 7000 < -30000 / 7000 := by norm_num
    have hexp : Real.exp (-40000 / 7000) < Real.exp (-30000 / 7000) :=
      Real.exp_lt_exp.mpr harg
    have hsub : Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000) < 0 :=
      sub_neg.mpr hexp
    have hE : ballisticK 1.225 7000 500 (Real.pi / 6) *
        (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000)) < 0 :=
      mul_neg_of_pos_of_neg hK hsub
    have hlt : Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) *
        (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000))) < 1 :=
      Real.exp_lt_one_iff.mpr hE
    unfold ballisticVelocity
    calc 3000 * Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) *
          (Real.exp (-40000 / 7000) - Real.exp (-30000 / 7000)))
        < 3000 * 1 := mul_lt_mul_of_pos_left hlt (by norm_num)
      _ = 3000 := mul_one _

-- The infinite-entry profile misses the entry speed at the entry altitude (about `2.84 km/s`
-- instead of `3 km/s`).
example :
    3000 * Real.exp (ballisticK 1.225 7000 500 (Real.pi / 6) * -Real.exp (-40000 / 7000)) ≠
      3000 := by
  have hsinpos : 0 < Real.sin (Real.pi / 6) := by rw [Real.sin_pi_div_six]; norm_num
  exact omitted_entry_term_ne (by norm_num) (by norm_num) (by norm_num) hsinpos (by norm_num) _

end PhyslibExtTest.Mechanics.EntryPorts
