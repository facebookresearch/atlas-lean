/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.NormalizedDifferenceIndex

/-!
# Remote sensing and radiometric inversion

Concrete consumers of `PhyslibExt.EarthScience.NormalizedDifferenceIndex`.

## i. Overview

Typical NDVI case, both endpoints, and the zero-signal exclusion is carried by the hypotheses.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks

## iv. References

- `PhyslibExt.EarthScience.NormalizedDifferenceIndex`
-/

/-- Typical case `r₁ = 0.8`, `r₂ = 0.2`: index `0.6 ∈ [-1, 1]`. -/
example : -1 ≤ (0.8 - 0.2 : ℝ) / (0.8 + 0.2) ∧ (0.8 - 0.2 : ℝ) / (0.8 + 0.2) ≤ 1 :=
  EarthScience.normalized_difference_index_mem (by norm_num) (by norm_num) (by norm_num)

/-- Endpoint `+1`: `r₁ = 0.5`, `r₂ = 0`. -/
example : (0.5 - 0 : ℝ) / (0.5 + 0) = 1 :=
  EarthScience.normalized_difference_index_eq_one (by norm_num)

/-- Endpoint `-1`: `r₁ = 0`, `r₂ = 0.5`. -/
example : (0 - 0.5 : ℝ) / (0 + 0.5) = -1 :=
  EarthScience.normalized_difference_index_eq_neg_one (by norm_num)
