/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.P07PhaseEquilibrium

open scoped Topology

/-!
# Clapeyron checks

Concrete consumers of `PhyslibExt.EarthScience.P07PhaseEquilibrium`:
the public shape of the Clapeyron theorem, the latent-heat form at
`T = 300` with `s2 - s1 = 10`, `v2 - v1 = 2` (so `dp / dT = 5`), and
the equal-entropy boundary `s2 = s1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Clapeyron shape
- B. Latent-heat form and equal-entropy boundary

## iv. References

- `PhyslibExt.EarthScience.P07PhaseEquilibrium`
-/

/-- Public shape of the Clapeyron theorem. -/
example {mu1 mu2 : ℝ → ℝ} {v1 v2 s1 s2 dp dT : ℝ} {t : ℝ}
    (hv : v2 - v1 ≠ 0) (hdT : dT ≠ 0)
    (hmu1 : HasDerivAt mu1 (v1 * dp - s1 * dT) t)
    (hmu2 : HasDerivAt mu2 (v2 * dp - s2 * dT) t)
    (hcoex : mu1 =ᶠ[𝓝 t] mu2) :
    dp / dT = (s2 - s1) / (v2 - v1) :=
  EarthScience.clapeyron_dp_dT hv hdT hmu1 hmu2 hcoex

/-- Latent-heat form, numeric: with `μ1 = μ2 = 3 * t`, `dp = 5`, `dT = 1`,
`s2 - s1 = 10`, `v2 - v1 = 2`, `T = 300`, `L = 3000`,
`dp / dT = 5 = 3000 / (300 * 2)`. -/
example : (5 : ℝ) / 1 = 3000 / (300 * (3 - 1)) :=
  EarthScience.clapeyron_latentHeat_form (mu1 := fun x : ℝ => 3 * x)
    (mu2 := fun x : ℝ => 3 * x) (v1 := 1) (v2 := 3) (s1 := 2) (s2 := 12)
    (dp := 5) (dT := 1) (T := 300) (L := 3000) (t := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [show ((1 : ℝ) * 5 - 2 * 1) = 3 by norm_num]
        simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (3 : ℝ))
    (by rw [show ((3 : ℝ) * 5 - 12 * 1) = 3 by norm_num]
        simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (3 : ℝ))
    (Filter.Eventually.of_forall fun _ => rfl) (by norm_num)

/-- Equal-entropy boundary: `s2 = s1` gives `dp / dT = 0` in latent-heat form. -/
example : (0 : ℝ) / 1 = 0 / (300 * (3 - 1)) :=
  EarthScience.clapeyron_latentHeat_form (mu1 := fun x : ℝ => -5 * x)
    (mu2 := fun x : ℝ => -5 * x) (v1 := 1) (v2 := 3) (s1 := 5) (s2 := 5)
    (dp := 0) (dT := 1) (T := 300) (L := 0) (t := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (-5 : ℝ))
    (by simpa using (hasDerivAt_id' (0 : ℝ)).const_mul (-5 : ℝ))
    (Filter.Eventually.of_forall fun _ => rfl) (by norm_num)
