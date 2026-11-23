/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ocean heat, salt, and nutrient budgets

Two fixed-volume boxes exchanging volume flux `Q` symmetrically obey
`V1 * S1' = Q * (S2 - S1) + F1` and `V2 * S2' = Q * (S1 - S2) + F2`,
where `F1, F2` are external fluxes. The total tracer stock
`V1 * S1 + V2 * S2` then changes only through `F1 + F2`; for a closed
system (`F1 = F2 = 0`) its derivative is `0`. Unequal volumes are
allowed. Stock is volume-weighted (and density-weighted if a mass
convention requires it); no external freshwater/salt flux is assumed.

## i. Overview

Multiply each box balance by its volume, add, and cancel the exchange
terms: `Q * (S2 - S1) + Q * (S1 - S2) = 0`.

## ii. Key results

- `EarthScience.two_box_total_stock_deriv`: total stock derivative is `F1 + F2`.
- `EarthScience.two_box_total_stock_deriv_closed`: closed total stock derivative is `0`.

## iii. Table of contents

- A. Two-box budgets

## iv. References

- `HasDerivAt.const_mul` / `HasDerivAt.add` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Two fixed-volume boxes exchanging volume flux `Q` symmetrically,
`V1 * S1' = Q * (S2 - S1) + F1`, `V2 * S2' = Q * (S1 - S2) + F2`:
the total tracer stock `V1 * S1 + V2 * S2` changes only through the
external fluxes `F1 + F2`. -/
theorem two_box_total_stock_deriv {V1 V2 Q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((Q * (S2 t - S1 t) + F1) / V1) t)
    (h2 : HasDerivAt S2 ((Q * (S1 t - S2 t) + F2) / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t := by
  have hV1' : V1 ≠ 0 := ne_of_gt hV1
  have hV2' : V2 ≠ 0 := ne_of_gt hV2
  have h := (h1.const_mul V1).add (h2.const_mul V2)
  have heq : V1 * ((Q * (S2 t - S1 t) + F1) / V1)
      + V2 * ((Q * (S1 t - S2 t) + F2) / V2) = F1 + F2 := by
    field_simp
    ring
  rwa [heq] at h

/-- Closed two-box exchange (`F1 = F2 = 0`): the total tracer stock has
derivative `0`, for unequal volumes and any `Q`. -/
theorem two_box_total_stock_deriv_closed {V1 V2 Q : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 (Q * (S2 t - S1 t) / V1) t)
    (h2 : HasDerivAt S2 (Q * (S1 t - S2 t) / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) 0 t := by
  have hV1' : V1 ≠ 0 := ne_of_gt hV1
  have hV2' : V2 ≠ 0 := ne_of_gt hV2
  have h := (h1.const_mul V1).add (h2.const_mul V2)
  have heq : V1 * (Q * (S2 t - S1 t) / V1) + V2 * (Q * (S1 t - S2 t) / V2) = 0 := by
    field_simp
    ring
  rwa [heq] at h

end EarthScience
