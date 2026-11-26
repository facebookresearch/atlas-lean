/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPStrideSum
import Mathlib.Tactic.NormNum

open MathlibExt.NumberTheory.LeonardoPWanted

-- The offset is strictly below p.
example : ∑ i ∈ Finset.range 3, leonardoPK 2 3 (3 * i + 1) = 43 := by
  calc
    _ = leonardoPK 2 3 8 - 6 := by
      have h := sum_leonardoPK_stride 2 3 1 2 (by decide) (by decide) (by decide)
      norm_num at h
      exact h
    _ = 43 := by decide

-- At offset p the endpoint is the next multiple of the stride.
example : ∑ i ∈ Finset.range 3, leonardoPK 2 3 (3 * i + 2) = 63 := by
  calc
    _ = leonardoPK 2 3 9 - 9 - 1 := by
      have h := sum_leonardoPK_stride 2 3 2 2 (by decide) (by decide) (by decide)
      norm_num at h
      exact h
    _ = 63 := by decide

-- The boundary formula also applies to a one-term sum at the smallest stride.
example : ∑ i ∈ Finset.range 1, leonardoPK 1 1 (2 * i + 1) = 1 := by
  calc
    _ = leonardoPK 1 1 2 - 1 - 1 := by
      have h := sum_leonardoPK_stride 1 1 1 0 (by decide) (by decide) (by decide)
      norm_num at h
      exact h
    _ = 1 := by decide
