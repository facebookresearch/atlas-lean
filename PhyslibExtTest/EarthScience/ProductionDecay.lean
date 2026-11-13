/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ProductionDecay

/-!
# Production-decay checks

Concrete consumers of `PhyslibExt.EarthScience.ProductionDecay`: a
numeric production-decay ODE, the initial value, and the no-production
reduction to the pure-decay derivative.

## i. Overview

These are elaboration and non-vacuity checks, not new results. Saturation
bounds are deferred by the production module and are not checked here.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Production-decay checks

## iv. References

- `PhyslibExt.EarthScience.ProductionDecay`
-/

/-! ## A. Production-decay checks -/

/-- Numeric production-decay ODE with `P = 4`, `λ = 2`, `N0 = 1`. -/
example (t : ℝ) : HasDerivAt
    (fun t : ℝ => 1 * Real.exp (-2 * t) + (4 / 2) * (1 - Real.exp (-2 * t)))
    (4 - 2 * (1 * Real.exp (-2 * t) + (4 / 2) * (1 - Real.exp (-2 * t)))) t :=
  EarthScience.production_decay_hasDerivAt 4 2 1 t (by norm_num)

/-- Numeric initial value: `N(0) = 1`. -/
example : (1 : ℝ) * Real.exp (-2 * 0) + (4 / 2) * (1 - Real.exp (-2 * 0)) = 1 :=
  EarthScience.production_decay_initial 4 2 1

/-- Degenerate case `P = 0`: the formula reduces to pure decay
`N(t) = N0*exp(-λ*t)` with derivative `-λ*N(t)`, stated in normalized form. -/
example (lam N0 t : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t : ℝ => N0 * Real.exp (-lam * t))
      (-lam * (N0 * Real.exp (-lam * t))) t := by
  simpa using EarthScience.production_decay_hasDerivAt 0 lam N0 t hlam
