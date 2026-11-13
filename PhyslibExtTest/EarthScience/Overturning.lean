/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.Overturning

/-!
# Overturning checks

Concrete consumers of `PhyslibExt.EarthScience.Overturning`:
the Stommel sign classification at `k = 1, alpha = 2e-4, beta = 8e-4`,
the public shapes of the closed-loop and one-edge conservation theorems,
and the flow-reversal boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`DeltaT = 10, DeltaS = 1` the exchange is `q = 0.0012 > 0`; with
`DeltaT = 0, DeltaS = 1` it is `q = -0.0008 < 0`; total salt is
conserved by exchange in both cases, in the closed loop and on one edge.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Stommel sign cases
- B. Conservation shapes and flow reversal

## iv. References

- `PhyslibExt.EarthScience.Overturning`
-/

/-- Shape of the Stommel sign classification at `DeltaT = 10, DeltaS = 1`. -/
example : (0 < (1 : ℝ) * ((2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1) ↔
      0 < (2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1) ∧
    ((1 : ℝ) * ((2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1) = 0 ↔
      (2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1 = 0) ∧
      ((1 : ℝ) * ((2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1) < 0 ↔
        (2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1 < 0) :=
  EarthScience.stommel_exchange_sign (show (0 : ℝ) < 1 by norm_num)

/-- Stommel sign, positive case `DeltaT = 10, DeltaS = 1`: the bracket is
`2e-4 * 10 - 8e-4 * 1 = 0.0012 > 0`, so `q > 0`. -/
example : 0 < (1 : ℝ) * ((2e-4 : ℝ) * 10 - (8e-4 : ℝ) * 1) :=
  (EarthScience.stommel_exchange_sign (show (0 : ℝ) < 1 by norm_num)).1.2 (by norm_num)

/-- Stommel sign, negative case `DeltaT = 0, DeltaS = 1`: the bracket is
`2e-4 * 0 - 8e-4 * 1 = -0.0008 < 0`, so `q < 0`. -/
example : (1 : ℝ) * ((2e-4 : ℝ) * 0 - (8e-4 : ℝ) * 1) < 0 :=
  (EarthScience.stommel_exchange_sign (show (0 : ℝ) < 1 by norm_num)).2.2.2 (by norm_num)

/-- Public shape of the closed-loop total-salt theorem: each balance has the incoming flux
`|q| * S_other` and the outgoing flux `|q| * S_self`. -/
example {V1 V2 q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ} (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((|q| * S2 t - |q| * S1 t) / V1 + F1 / V1) t)
    (h2 : HasDerivAt S2 ((|q| * S1 t - |q| * S2 t) / V2 + F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t :=
  EarthScience.overturning_total_salt_deriv hV1 hV2 h1 h2

/-- Public shape of the one-edge total-salt theorem. -/
example {V1 V2 q F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ} (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 ((if 0 ≤ q then -q * S1 t else -q * S2 t) / V1 + F1 / V1) t)
    (h2 : HasDerivAt S2 ((if 0 ≤ q then q * S1 t else q * S2 t) / V2 + F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t :=
  EarthScience.one_edge_upwind_total_salt_deriv hV1 hV2 h1 h2

/-- Public shape of the flow-reversal (`q = 0`) theorem. -/
example {V1 V2 F1 F2 : ℝ} {S1 S2 : ℝ → ℝ} {t : ℝ} (hV1 : 0 < V1) (hV2 : 0 < V2)
    (h1 : HasDerivAt S1 (F1 / V1) t) (h2 : HasDerivAt S2 (F2 / V2) t) :
    HasDerivAt (fun t => V1 * S1 t + V2 * S2 t) (F1 + F2) t :=
  EarthScience.overturning_total_salt_deriv_zero_q hV1 hV2 h1 h2

/-- Negative-exchange numeric case on one edge: exchange terms still cancel. -/
example : (2 : ℝ) * ((-(-8e-4 : ℝ)) * 35 / 2) + 3 * ((-8e-4 : ℝ) * 35 / 3) = 0 := by
  norm_num

/-- Negative-exchange numeric case in the closed loop (`q = -8e-4`, `S1 = 35`, `S2 = 36`):
box 1 gains `|q| * 36` and loses `|q| * 35`, box 2 the reverse, and the terms cancel. -/
example : (2 : ℝ) * ((|(-8e-4 : ℝ)| * 36 - |(-8e-4 : ℝ)| * 35) / 2) +
    3 * ((|(-8e-4 : ℝ)| * 35 - |(-8e-4 : ℝ)| * 36) / 3) = 0 := by
  ring
