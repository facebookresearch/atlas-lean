/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Sverdrup

/-!
# Wind-driven gyres and vorticity balance

Concrete consumers of `PhyslibExt.EarthScience.Sverdrup`.

## i. Overview

Numeric Sverdrup transport and the zero-curl boundary.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.Sverdrup`
-/

/-- Numeric Sverdrup: `β = 2`, `curl = 6`, `ρ₀ = 3` gives `V = 1`. -/
example : (1 : ℝ) = 6 / (3 * 2) :=
  EarthScience.sverdrup_transport (by norm_num) (by norm_num) (by norm_num)

/-- Zero curl gives zero transport. -/
example : (0 : ℝ) = 0 :=
  EarthScience.sverdrup_zero_curl (β := 2) (V := 0) (ρ₀ := 3) (by norm_num) (by norm_num) (by norm_num)
