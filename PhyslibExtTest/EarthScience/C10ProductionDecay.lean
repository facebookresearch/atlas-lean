/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C10ProductionDecay

/-!
# Production-decay checks

Concrete consumers of `PhyslibExt.EarthScience.C10ProductionDecay`: a
numeric production-decay ODE, the initial value, the no-production
reduction to pure decay, and the saturation value `P/λ`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`P = 4`, `λ = 2`, `N0 = 1`, the saturation inventory is `P/λ = 2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C10ProductionDecay`
-/

/-- Numeric production-decay ODE with `P = 4`, `λ = 2`, `N0 = 1`. -/
example (t : ℝ) : HasDerivAt
    (fun t : ℝ => 1 * Real.exp (-2 * t) + (4 / 2) * (1 - Real.exp (-2 * t)))
    (4 - 2 * (1 * Real.exp (-2 * t) + (4 / 2) * (1 - Real.exp (-2 * t)))) t :=
  EarthScience.production_decay_hasDerivAt 4 2 1 t (by norm_num)

/-- Numeric initial value: `N(0) = 1`. -/
example : (1 : ℝ) * Real.exp (-2 * 0) + (4 / 2) * (1 - Real.exp (-2 * 0)) = 1 :=
  EarthScience.production_decay_initial 4 2 1

/-- Degenerate case `P = 0`: pure decay, `N(t) = N0*exp(-λ*t)`. -/
example (lam N0 t : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t : ℝ => N0 * Real.exp (-lam * t) +
        (0 / lam) * (1 - Real.exp (-lam * t)))
      (0 - lam * (N0 * Real.exp (-lam * t) +
        (0 / lam) * (1 - Real.exp (-lam * t)))) t :=
  EarthScience.production_decay_hasDerivAt 0 lam N0 t hlam
