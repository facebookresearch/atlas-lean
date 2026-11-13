/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.NutrientBiomass

/-!
# Nutrient-biomass checks

Concrete consumers of `PhyslibExt.EarthScience.NutrientBiomass`:
the public shapes of the three theorems, Michaelis-Menten uptake at
`umax = 2, K = 1, N = 1`, and the zero-nutrient boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At
`umax = 2, K = 1, N = 1` the uptake is `2 * 1 / (1 + 1) = 1`, inside
`[0, 2]`; at `N = 0` it is `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conservation shape
- B. Michaelis-Menten numeric case and zero-nutrient boundary

## iv. References

- `PhyslibExt.EarthScience.NutrientBiomass`
-/

open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)

/-- Public shape of the conservation theorem. -/
example {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt (fun t => N t + B t) 0 t :=
  EarthScience.nutrient_biomass_conservation hN hB

/-- Michaelis-Menten at `umax = 2, K = 1, N = 1`: uptake `1`, inside `[0, 2]`. -/
example : 0 ≤ mmRate (2 : ℝ) 1 1 ∧ mmRate (2 : ℝ) 1 1 ≤ 2 :=
  EarthScience.michaelis_menten_bounds (by norm_num) (by norm_num) (by norm_num)

/-- The uptake value at `umax = 2, K = 1, N = 1` is `2 * 1 / (1 + 1) = 1`. -/
example : mmRate (2 : ℝ) 1 1 = 1 := by norm_num [mmRate]

/-- The bounds hold at the endpoint `umax = 0`, where the uptake is `0`. -/
example : 0 ≤ mmRate (0 : ℝ) 1 1 ∧ mmRate (0 : ℝ) 1 1 ≤ 0 :=
  EarthScience.michaelis_menten_bounds le_rfl (by norm_num) (by norm_num)

/-- Zero nutrient: uptake `0`. -/
example : mmRate (2 : ℝ) 1 0 = 0 := by norm_num [mmRate]

/-- Public shape of the zero-nutrient boundary theorem. -/
example {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hu0 : u 0 = 0) (hNt : N t = 0)
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt B (-r * B t) t ∧ HasDerivAt N (r * B t) t :=
  EarthScience.nutrient_biomass_zero_nutrient hu0 hNt hN hB
