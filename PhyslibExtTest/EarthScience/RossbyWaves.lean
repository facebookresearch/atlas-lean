/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RossbyWaves

/-!
# Rossby-wave checks

Concrete consumers of `PhyslibExt.EarthScience.RossbyWaves`:
the public shapes of the three theorems, the dispersion relation at
`U = 10, beta = 0, k = 1, l = 0`, and the `beta = 0` / zero-flow
boundaries.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`beta = 0` the mode is pure advection, `omega = U * k`; with `U = 0`
it is `omega = -beta * k / (k^2 + l^2)`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Dispersion shapes
- B. Advection and zero-flow boundaries

## iv. References

- `PhyslibExt.EarthScience.RossbyWaves`
-/

/-- Public shape of the dispersion theorem. -/
example {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k :=
  EarthScience.rossby_dispersion h homega

/-- Public shape of the dispersion iff theorem. -/
example {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0) :
    omega = U * k - beta * k / (k ^ 2 + l ^ 2) ↔
      (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k :=
  EarthScience.rossby_dispersion_iff h

/-- `beta = 0`: pure advection `omega = U * k`. -/
example : (10 : ℝ) * 1 - 0 * 1 / (1 ^ 2 + 0 ^ 2) = 10 * 1 := by norm_num

/-- `U = 0`: `omega = -beta * k / (k^2 + l^2)`. -/
example {beta k l : ℝ} :
    (0 : ℝ) * k - beta * k / (k ^ 2 + l ^ 2) = -beta * k / (k ^ 2 + l ^ 2) := by
  ring

/-- Public shape of the phase-speed theorem. -/
example {U beta k l omega : ℝ} (hk : k ≠ 0) (h : k ^ 2 + l ^ 2 ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    omega / k = U - beta / (k ^ 2 + l ^ 2) :=
  EarthScience.rossby_phase_speed hk h homega
