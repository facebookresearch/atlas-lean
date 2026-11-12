/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.O06TwoBoxBudgets

/-!
# Two-box budget checks

Concrete consumers of `PhyslibExt.EarthScience.O06TwoBoxBudgets`:
the public shapes of both theorems, the closed-system numeric
cancellation `2 * (-1 / 4) + 3 * (1 / 6) = 0`, and the zero-exchange
boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`V1 = 2, V2 = 3, Q = 1 / 2, S1 = 35, S2 = 34`, the box derivatives are
`Q * (S2 - S1) / V1 = -1 / 4` and `Q * (S1 - S2) / V2 = 1 / 6`, and
the volume-weighted total derivative is `2 * (-1 / 4) + 3 * (1 / 6) = 0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-box exchange shapes
- B. Closed numeric cancellation and zero exchange

## iv. References

- `PhyslibExt.EarthScience.O06TwoBoxBudgets`
-/

/-- Public shape of the two-box theorem with external fluxes. -/
example {V1 V2 Q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ} (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((Q * (S2 t - S1 t) + F1) / V1) t)
    (h2 : HasDerivAt S2 ((Q * (S1 t - S2 t) + F2) / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t :=
  EarthScience.two_box_total_stock_deriv hV1 hV2 h1 h2

/-- Public shape of the closed two-box theorem. -/
example {V1 V2 Q : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ} (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 (Q * (S2 t - S1 t) / V1) t)
    (h2 : HasDerivAt S2 (Q * (S1 t - S2 t) / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) 0 t :=
  EarthScience.two_box_total_stock_deriv_closed hV1 hV2 h1 h2

/-- Closed numeric cancellation: `V1 = 2, V2 = 3, Q = 1/2, S1 = 35, S2 = 34`. -/
example : (2 : ℝ) * ((1 / 2) * (34 - 35) / 2) + 3 * ((1 / 2) * (35 - 34) / 3) = 0 := by
  norm_num

/-- Zero exchange (`Q = 0`) with external fluxes: total derivative is `F1 + F2`. -/
example {F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ}
    (h1 : HasDerivAt S1 (F1 / 2) t) (h2 : HasDerivAt S2 (F2 / 3) t) :
    HasDerivAt (fun t => (2 : ℝ) * S1 t + 3 * S2 t) (F1 + F2) t := by
  have h1' : HasDerivAt S1 ((((0 : ℝ) * (S2 t - S1 t) + F1) / 2)) t := by
    simpa using h1
  have h2' : HasDerivAt S2 ((((0 : ℝ) * (S1 t - S2 t) + F2) / 3)) t := by
    simpa using h2
  exact EarthScience.two_box_total_stock_deriv (by norm_num) (by norm_num) h1' h2'
