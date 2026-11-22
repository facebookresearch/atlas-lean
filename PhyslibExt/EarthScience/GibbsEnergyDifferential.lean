/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Tactic.LinearCombination
/-!
# Legendre transformation yields the differential of Gibbs energy

With `G = U - T * S + p * V`, the product rule gives
`dG = dU - T * dS - S * dT + p * dV + V * dp`. Combined with the
fundamental relation `dU = T * dS - p * dV`, this yields
`dG = -S * dT + V * dp`.

## i. Overview

The theorem is the linear-algebra consequence of the two differential
identities: substituting `dU` into the product-rule form cancels the
`T * dS` and `p * dV` terms. No claim is made about integrability,
Maxwell relations, or any particular equation of state.

## ii. Key results

- `EarthScience.gibbs_energy_differential`: `dG = -S * dT + V * dp`.

## iii. References

- `linear_combination` in Mathlib (`Mathlib/Tactic/LinearCombination.lean`).
-/

@[expose] public section

namespace EarthScience

/-- Legendre transformation to Gibbs energy: with `G = U - T * S + p * V`,
the differential identity `dU = T * dS - p * dV` and the product-rule form
`dG = dU - T * dS - S * dT + p * dV + V * dp` give `dG = -S * dT + V * dp`. -/
theorem gibbs_energy_differential {dU dS dV dT dp dG T p S V : ℝ}
    (hU : dU = T * dS - p * dV)
    (hG : dG = dU - T * dS - S * dT + p * dV + V * dp) :
    dG = -S * dT + V * dp := by
  linear_combination hG + hU

end EarthScience
