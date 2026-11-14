/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GumbelQuantile

/-!
# Gumbel-quantile checks

Concrete consumers of `PhyslibExt.EarthScience.GumbelQuantile`:
the standard Gumbel (`μ = 0`, `β = 1`) quantile at `q = exp(-1)` is `0`,
a fitted Gumbel (`μ = 2`, `β = 3`) round-trips at `q = 0.9` and at
`x = 5`, and the CDF at `0` round-trips through the quantile.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete quantile values
- B. Round-trips

## iv. References

- `PhyslibExt.EarthScience.GumbelQuantile`
-/

/-- Standard Gumbel: the quantile at `q = exp(-1)` is `0`. -/
example : EarthScience.gumbelQuantile 0 1 (Real.exp (-1)) = 0 := by
  simp [EarthScience.gumbelQuantile]

/-- Fitted Gumbel (`μ = 2`, `β = 3`): the CDF at the `0.9`-quantile is `0.9`. -/
example :
    EarthScience.gumbelCDF 2 3 (EarthScience.gumbelQuantile 2 3 0.9) = 0.9 :=
  EarthScience.gumbelQuantile_inverts_cdf (by norm_num) (by norm_num) (by norm_num)

/-- Fitted Gumbel (`μ = 2`, `β = 3`): the quantile at `CDF(5)` is `5`. -/
example :
    EarthScience.gumbelQuantile 2 3 (EarthScience.gumbelCDF 2 3 5) = 5 :=
  EarthScience.gumbelCDF_inverts_quantile (by norm_num)

/-- Boundary-adjacent round-trip: standard Gumbel quantile at `CDF(0)` is `0`. -/
example :
    EarthScience.gumbelQuantile 0 1 (EarthScience.gumbelCDF 0 1 0) = 0 :=
  EarthScience.gumbelCDF_inverts_quantile (by norm_num)
