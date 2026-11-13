/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-!
# Biogeochemical productivity and resource limits

For the closed nutrient-biomass model `N' = -u(N) * B + r * B` and
`B' = u(N) * B - r * B`, the total `N + B` is constant (derivative
`0`), with one nutrient-equivalent unit on both compartments. For
Michaelis-Menten uptake `u = MichaelisMenten.mmRate umax K`, the bound
`0 ≤ u(N) ≤ umax` (`umax >= 0`, `K > 0`, `N >= 0`) is
`MichaelisMenten.mmRate_nonneg_and_le`. At zero nutrient (with `u(0) = 0`)
the derivatives of biomass and nutrient are `-r * B` and `r * B`. The
stoichiometric conversion between mass and mole units is explicit in the
model convention; no empirical stoichiometric claim is made here.

## i. Overview

The model is the closed nutrient-phytoplankton-zooplankton framework of
Franks (2002) without zooplankton, written in nutrient (nitrogen) units:
`N` is the dissolved nutrient, `B` the phytoplankton biomass in the same
units (unit stoichiometry: one unit of nutrient taken up becomes one unit
of biomass), `u(N)` the uptake rate per unit biomass, and `r` the biomass
loss rate (respiration and mortality), whose losses return to the nutrient
pool at once (complete recycling, no export). Adding the two balance
equations cancels uptake and recycling exactly, so total nutrient is
conserved. Michaelis-Menten uptake is the canonical rate
`MichaelisMenten.mmRate`, whose bounds (`mmRate_lt`,
`mmRate_nonneg_and_le`) live with it in `MathlibExt`. The zero-nutrient
identities hold for all real `r` and `B t`; no sign is asserted
(`-r * B t ≤ 0 ≤ r * B t` would need `0 ≤ r` and `0 ≤ B t`, which are not
assumed).

## ii. Key results

- `EarthScience.nutrient_biomass_conservation`: `N + B` has derivative `0`.
- `EarthScience.nutrient_biomass_zero_nutrient`: the derivative identities at zero nutrient.

## iii. Table of contents

- A. Nutrient-biomass conservation
- B. Zero-nutrient boundary

## iv. References

- P. J. S. Franks, *NPZ models of plankton dynamics: their construction, coupling to
  physics, and application*, J. Oceanogr. 58 (2002), 379–387: closed
  nutrient-phytoplankton-zooplankton models in nitrogen units, in which uptake moves
  nitrogen from the nutrient pool to phytoplankton and losses return it, so the balances
  sum to zero and total nitrogen is conserved.
- `MathlibExt.Biology.Dynamics.MichaelisMenten` (`mmRate`, `mmRate_lt`,
  `mmRate_nonneg_and_le`) for the Michaelis-Menten uptake law and its bounds.
-/

@[expose] public section

namespace EarthScience

/-- Closed nutrient-biomass model `N' = -u(N) * B + r * B`,
`B' = u(N) * B - r * B` (the model of Franks (2002) without zooplankton): the total
`N + B` (one nutrient-equivalent unit on both compartments) has derivative `0`. -/
theorem nutrient_biomass_conservation {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt (fun t => N t + B t) 0 t := by
  have h := hN.add hB
  have hsum : (-(u (N t)) * B t + r * B t) + (u (N t) * B t - r * B t) = 0 := by
    ring
  rw [hsum] at h
  exact h

/-- Boundary case: at zero nutrient, with `u(0) = 0`, the derivative of biomass is
`-r * B t` (respiration only) and the derivative of nutrient is `r * B t`. These are
identities for all real `r` and `B t`; no sign is asserted. -/
lemma nutrient_biomass_zero_nutrient {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hu0 : u 0 = 0) (hNt : N t = 0)
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt B (-r * B t) t ∧ HasDerivAt N (r * B t) t := by
  have hB' : u (N t) * B t - r * B t = -r * B t := by rw [hNt, hu0]; ring
  have hN' : -(u (N t)) * B t + r * B t = r * B t := by rw [hNt, hu0]; ring
  rw [hB'] at hB
  rw [hN'] at hN
  exact ⟨hB, hN⟩

end EarthScience
