/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.FundamentalDiagram

/-!
# Greenshields flux checks

Concrete consumers of `PhyslibExt.FluidDynamics.Traffic.FundamentalDiagram`:
with free-flow speed `100` and jam density `200`, the flux is `0` at
densities `0` and `200`, and reaches the capacity `5000` at density `100`.
At density `300`, outside the physical range, the formula is negative,
which is why the range theorem assumes `k ≤ kj`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Endpoint, midpoint, and capacity values
- B. Outside the physical range
- C. Public theorem shape

## iv. References

- `PhyslibExt.FluidDynamics.Traffic.FundamentalDiagram`
-/

open FluidDynamics.Traffic

/-! ## A. Endpoint, midpoint, and capacity values -/

/-- Zero density and jam density both give zero flux. -/
example : greenshieldsFlux 100 200 0 = 0 ∧ greenshieldsFlux 100 200 200 = 0 := by
  constructor <;> norm_num [greenshieldsFlux]

/-- Midpoint value at half the jam density, through the public lemma. -/
example : greenshieldsFlux 100 200 (200 / 2) = 5000 := by
  have h := greenshieldsFlux_half (vf := (100 : ℝ)) (kj := (200 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- Range bounds at the midpoint witness. -/
example : 0 ≤ greenshieldsFlux 100 200 100
    ∧ greenshieldsFlux 100 200 100 ≤ 100 * 200 / 4 :=
  greenshieldsFlux_nonneg_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## B. Outside the physical range -/

/-- Past jam density the closed form is negative, so the density-range
hypotheses cannot be dropped. -/
example : greenshieldsFlux 100 200 300 = -15000 := by
  norm_num [greenshieldsFlux]

/-! ## C. Public theorem shape -/

/-- The public statements, restated through the definition. -/
example {vf kj k : ℝ} (hvf : 0 < vf) (hkj : 0 < kj) (hk0 : 0 ≤ k) (hk : k ≤ kj) :
    0 ≤ vf * k * (1 - k / kj) ∧ vf * k * (1 - k / kj) ≤ vf * kj / 4 :=
  greenshieldsFlux_nonneg_le hvf hkj hk0 hk

/-- Capacity attainment at the same witness, through the public theorem. -/
example : greenshieldsFlux 100 200 (200 / 2) = 100 * 200 / 4
    ∧ ∀ k : ℝ, 0 ≤ k → k ≤ 200 → greenshieldsFlux 100 200 k ≤ 100 * 200 / 4 :=
  greenshieldsFlux_capacity_attained (by norm_num) (by norm_num)
