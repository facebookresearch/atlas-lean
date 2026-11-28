/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.JExpansion

open UpperHalfPlane

#check @ModularCurve.qExpansion_E4_eq_map_eisenstein4
#check @ModularCurve.eisenstein6
#check @ModularCurve.constantCoeff_eisenstein6
#check @ModularCurve.qExpansion_E6_eq_map_eisenstein6

/-- The constant term of the `q`-expansion of `E₆` is `1`. -/
example : PowerSeries.constantCoeff (qExpansion 1 ⇑ModularForm.E₆) = 1 := by
  rw [ModularCurve.qExpansion_E6_eq_map_eisenstein6, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    ModularCurve.constantCoeff_eisenstein6, map_one]

/-- The coefficient of `q` in the `q`-expansion of `E₆` is `-504`. -/
example : PowerSeries.coeff 1 (qExpansion 1 ⇑ModularForm.E₆) = -504 := by
  rw [ModularCurve.qExpansion_E6_eq_map_eisenstein6, PowerSeries.coeff_map,
    ModularCurve.eisenstein6, PowerSeries.coeff_mk]
  norm_num

/-- The coefficient of `q` in the `q`-expansion of `E₄` is `240`. -/
example : PowerSeries.coeff 1 (qExpansion 1 ⇑ModularForm.E₄) = 240 := by
  rw [ModularCurve.qExpansion_E4_eq_map_eisenstein4, PowerSeries.coeff_map,
    ModularCurve.eisenstein4, PowerSeries.coeff_mk]
  norm_num
