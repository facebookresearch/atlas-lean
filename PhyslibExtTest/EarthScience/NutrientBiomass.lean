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
the public shapes of the conservation theorem and of the zero-nutrient
boundary lemma. The Michaelis-Menten uptake bounds are tested with
`MathlibExt.Biology.Dynamics.MichaelisMenten` in `MathlibExtTest`.

## i. Overview

These are elaboration checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Conservation shape
- B. Zero-nutrient boundary

## iv. References

- `PhyslibExt.EarthScience.NutrientBiomass`
-/

/-- Public shape of the conservation theorem. -/
example {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt (fun t => N t + B t) 0 t :=
  EarthScience.nutrient_biomass_conservation hN hB

/-- Public shape of the zero-nutrient boundary theorem. -/
example {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hu0 : u 0 = 0) (hNt : N t = 0)
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt B (-r * B t) t ∧ HasDerivAt N (r * B t) t :=
  EarthScience.nutrient_biomass_zero_nutrient hu0 hNt hN hB
