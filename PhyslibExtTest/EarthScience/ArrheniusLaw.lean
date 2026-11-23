/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ArrheniusLaw

/-!
# Arrhenius law checks

Concrete consumers of `PhyslibExt.EarthScience.ArrheniusLaw`: with a dimensionless
prefactor `A = 1`, `Ea = 1000`, `R = 8.314`, the rate at `T = 400` exceeds the rate at
`T = 300`, and the rate at `T = 300` is positive; a first-order prefactor of dimension
time⁻¹ gives a positive rate; and the typed factor is the raw `exp(-(Ea / (R * T)))` on
coordinates.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ArrheniusLaw`
-/

open Units.QuantityDimensions

/-- `k(300) < k(400)` for `A = 1`, `Ea = 1000`, `R = 8.314`. -/
example :
    (⟨1⟩ : WithDim dimensionlessDim ℝ).val *
        expScaledEnergy ⟨1000⟩ ⟨8.314⟩ ⟨300⟩ (by norm_num) (by norm_num) <
      (⟨1⟩ : WithDim dimensionlessDim ℝ).val *
        expScaledEnergy ⟨1000⟩ ⟨8.314⟩ ⟨400⟩ (by norm_num) (by norm_num) :=
  EarthScience.arrhenius_strictMono (A := (⟨1⟩ : WithDim dimensionlessDim ℝ))
    (Ea := ⟨1000⟩) (R := ⟨8.314⟩) (by norm_num) (by norm_num) (by norm_num)
    (show (⟨⟨300⟩, by norm_num⟩ : {T : WithDim temperatureDim ℝ // 0 < T.val}) <
      ⟨⟨400⟩, by norm_num⟩ by norm_num)

/-- `k(300) > 0` for the same parameters. -/
example :
    0 < (⟨1⟩ : WithDim dimensionlessDim ℝ).val *
      expScaledEnergy ⟨1000⟩ ⟨8.314⟩ ⟨300⟩ (by norm_num) (by norm_num) :=
  EarthScience.arrhenius_pos (by norm_num) _ _ _

/-- A first-order rate constant `A = 2` of dimension time⁻¹ gives a positive rate, e.g. at
`T = 1`. -/
example :
    0 < (⟨2⟩ : WithDim (Dimension.single ISQDimensionBase.time)⁻¹ ℝ).val *
      expScaledEnergy ⟨500⟩ ⟨10⟩ ⟨1⟩ (by norm_num) (by norm_num) :=
  EarthScience.arrhenius_pos (by norm_num) _ _ _

/-- The typed factor is `exp(-(Ea / (R * T)))` on coordinates. -/
example :
    expScaledEnergy (⟨1000⟩ : WithDim molarEnergyDim ℝ) ⟨8.314⟩ ⟨300⟩ (by norm_num)
        (by norm_num) =
      Real.exp (-(1000 / (8.314 * 300))) :=
  expScaledEnergy_val _ _ _ _ _
