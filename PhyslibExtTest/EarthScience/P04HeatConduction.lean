/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.P04HeatConduction

/-!
# Slab conduction checks

Concrete consumers of `PhyslibExt.EarthScience.P04HeatConduction`:
`T0 = 0`, `TL = 10`, `L = 2`, `k = 3` (so `T(z) = 5 * z`, `T' = 5`,
`q = -15`), the uniform-temperature boundary `TL = T0`, and the
reversed-gradient boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric slab
- B. Uniform and reversed-gradient boundaries

## iv. References

- `PhyslibExt.EarthScience.P04HeatConduction`
-/

/-- Numeric slab boundary values. -/
example : (fun z => (0 : ℝ) + (10 - 0) * z / 2) 0 = 0 ∧
    (fun z => (0 : ℝ) + (10 - 0) * z / 2) 2 = 10 :=
  EarthScience.slab_profile_boundary (by norm_num)

/-- Numeric slab at `z = 1`: temperature `5`. -/
example : (fun z => (0 : ℝ) + (10 - 0) * z / 2) 1 = 5 := by norm_num

/-- Numeric slab derivative `T' = 5`. -/
example (z : ℝ) :
    HasDerivAt (fun z => (0 : ℝ) + (10 - 0) * z / 2) ((10 - 0) / 2) z :=
  EarthScience.hasDerivAt_slab_profile (by norm_num) z

/-- Numeric slab: second derivative `0` and flux `-15`. -/
example (z : ℝ) :
    iteratedDeriv 2 (fun z => (0 : ℝ) + (10 - 0) * z / 2) z = 0 ∧
      -(3 : ℝ) * deriv (fun z => (0 : ℝ) + (10 - 0) * z / 2) z = -15 := by
  have h := EarthScience.slab_profile_second_deriv (T0 := 0) (TL := 10) (L := 2) (k := 3)
    (by norm_num) z
  refine ⟨h.1, ?_⟩
  rw [h.2]
  norm_num

/-- Uniform-temperature boundary: `TL = T0` gives constant profile, zero flux. -/
example (z : ℝ) :
    HasDerivAt (fun z => (5 : ℝ) + (5 - 5) * z / 2) ((5 - 5) / 2) z :=
  EarthScience.hasDerivAt_slab_profile (by norm_num) z

/-- Reversed-gradient boundary: `TL < T0` gives a negative derivative. -/
example (z : ℝ) :
    HasDerivAt (fun z => (10 : ℝ) + (0 - 10) * z / 2) ((0 - 10) / 2) z :=
  EarthScience.hasDerivAt_slab_profile (by norm_num) z
