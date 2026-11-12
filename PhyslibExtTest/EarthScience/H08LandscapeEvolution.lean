/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.H08LandscapeEvolution

/-!
# Steady hillslope profile checks

Concrete consumers of `PhyslibExt.EarthScience.H08LandscapeEvolution`:
`U = 2, D = 1, L = 3` (so `z(x) = 9 - x ^ 2`, `z'(x) = -2 * x`,
`z'' = -2`), the no-uplift boundary `U = 0`, and a second
non-vacuous profile `U = 1, D = 2, L = 4`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric profile `U = 2, D = 1, L = 3`
- B. No-uplift and second-profile boundaries

## iv. References

- `PhyslibExt.EarthScience.H08LandscapeEvolution`
-/

/-- Numeric profile boundary: `z(3) = z(-3) = 0`. -/
example : (2 : ℝ) * ((3 : ℝ) ^ 2 - (3 : ℝ) ^ 2) / (2 * 1) = 0 ∧
    (2 : ℝ) * ((3 : ℝ) ^ 2 - (-(3 : ℝ)) ^ 2) / (2 * 1) = 0 :=
  EarthScience.h08_profile_boundary (by norm_num) (by norm_num) (by norm_num)

/-- Numeric profile at `x = 0`: `z(0) = 9`. -/
example : (2 : ℝ) * ((3 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / (2 * 1) = 9 :=
  EarthScience.h08_profile_witness

/-- Numeric profile at `x = 1`: `z(1) = 8`. -/
example : (2 : ℝ) * ((3 : ℝ) ^ 2 - (1 : ℝ) ^ 2) / (2 * 1) = 8 := by norm_num

/-- Numeric profile derivative at `x = 1`: `z'(1) = -2`. -/
example :
    HasDerivAt (fun x => (2 : ℝ) * ((3 : ℝ) ^ 2 - x ^ 2) / (2 * 1)) (-(2 : ℝ) * 1 / 1) 1 :=
  EarthScience.h08_profile_hasDerivAt (L := 3) (by norm_num) (by norm_num) (by norm_num) 1

/-- Numeric profile steadiness: `z'' = -2` and `U + D * z'' = 0`. -/
example :
    HasDerivAt (fun x => -(2 : ℝ) * x / 1) (-(2 : ℝ) / 1) 1 ∧
      (2 : ℝ) + 1 * (-(2 : ℝ) / 1) = 0 :=
  EarthScience.h08_profile_steady (L := 3) (by norm_num) (by norm_num) (by norm_num) 1

/-- No uplift: the zero profile has derivative `0`. -/
example (x : ℝ) :
    HasDerivAt (fun x => (0 : ℝ) * ((3 : ℝ) ^ 2 - x ^ 2) / (2 * 1)) (-(0 : ℝ) * x / 1) x :=
  EarthScience.h08_profile_hasDerivAt (L := 3) (by norm_num) (by norm_num) (by norm_num) x

/-- Second profile `U = 1, D = 2, L = 4`: `z(0) = 4`, `z(4) = 0`. -/
example : (1 : ℝ) * ((4 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / (2 * 2) = 4 ∧
    (1 : ℝ) * ((4 : ℝ) ^ 2 - (4 : ℝ) ^ 2) / (2 * 2) = 0 := by
  constructor
  · norm_num
  · norm_num
