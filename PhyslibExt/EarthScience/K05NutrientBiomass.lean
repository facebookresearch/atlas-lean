/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Ring

/-!
# Biogeochemical productivity and resource limits

For the closed nutrient-biomass model `N' = -u(N) * B + r * B` and
`B' = u(N) * B - r * B`, the total `N + B` is constant (derivative
`0`), with one nutrient-equivalent unit on both compartments. The
Michaelis-Menten uptake `u(N) = umax * N / (K + N)` with `K > 0`,
`N >= 0` stays in `[0, umax]`, and at zero nutrient biomass decays at
rate `-r * B` while nutrient grows at `r * B`. The stoichiometric
conversion between mass and mole units is explicit in the model
convention; no empirical stoichiometric claim is made here.

## i. Overview

Adding the two balance equations cancels uptake and respiration
exactly. The Michaelis-Menten bounds follow from `0 < K + N` and
`N <= K + N`.

## ii. Key results

- `EarthScience.nutrient_biomass_conservation`: `N + B` has derivative `0`.
- `EarthScience.michaelis_menten_bounds`: uptake stays in `[0, umax]`.
- `EarthScience.nutrient_biomass_zero_nutrient`: zero-nutrient boundary.

## iii. Table of contents

- A. Nutrient-biomass conservation
- B. Michaelis-Menten uptake and zero-nutrient boundary

## iv. References

- `HasDerivAt.add` in Mathlib.
- `div_nonneg` / `div_le_iff₀` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Closed nutrient-biomass model `N' = -u(N) * B + r * B`,
`B' = u(N) * B - r * B`: the total `N + B` (one nutrient-equivalent
unit on both compartments) has derivative `0`. -/
theorem nutrient_biomass_conservation {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
    (hN : HasDerivAt N (-(u (N t)) * B t + r * B t) t)
    (hB : HasDerivAt B (u (N t) * B t - r * B t) t) :
    HasDerivAt (fun t => N t + B t) 0 t := by
  have h := hN.add hB
  have hsum : (-(u (N t)) * B t + r * B t) + (u (N t) * B t - r * B t) = 0 := by
    ring
  rw [hsum] at h
  exact h

/-- Michaelis-Menten uptake `u(N) = umax * N / (K + N)` with
`umax >= 0`, `K > 0`, `N >= 0` stays in `[0, umax]`; in particular
`u(0) = 0`. -/
theorem michaelis_menten_bounds {umax K N : ℝ} (humax : 0 ≤ umax) (hK : 0 < K)
    (hN : 0 ≤ N) :
    0 ≤ umax * N / (K + N) ∧ umax * N / (K + N) ≤ umax := by
  have hD : 0 < K + N := add_pos_of_pos_of_nonneg hK hN
  constructor
  · exact div_nonneg (mul_nonneg humax hN) (le_of_lt hD)
  · rw [div_le_iff₀ hD]
    have hNK : N ≤ K + N := le_add_of_nonneg_left (le_of_lt hK)
    exact mul_le_mul_of_nonneg_left hNK humax

/-- Boundary case: at zero nutrient, with `u(0) = 0`, biomass decays at
rate `-r * B` (respiration only) and nutrient grows at `r * B`. -/
theorem nutrient_biomass_zero_nutrient {N B : ℝ → ℝ} {u : ℝ → ℝ} {r : ℝ} {t : ℝ}
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
