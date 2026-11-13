/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DividendGordon
import Mathlib.Tactic.NormNum

/-!
# Tests for gordon formula for constant-growth dividends

Tests for the Gordon formula for constant-growth dividends: `D₁ = 12`, `r = 1/10`,
`g = 1/20` is worth `240`; the first-payment-only branch `g = -1` is worth `5/2`; and
the identification applied to a concrete growing perpetuity.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.DividendGordon

open MathlibExt.Economics.Finance
open MathlibExt.Economics.Finance.DividendGordon

example : ∑' t, discountedDividendStream 12 (1/10) (1/20) t = 240 := by
  have h : ∑' t, discountedDividendStream 12 (1/10) (1/20) t = 12 / (1/10 - 1/20) :=
    dividendGordon_tsum (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

example : ∑' t, discountedDividendStream 5 1 (-1) t = 5 / 2 := by
  have h : ∑' t, discountedDividendStream 5 1 (-1) t = 5 / (1 - -1) :=
    dividendGordon_tsum (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

example : dividendStream 12 (1/20) 0 = 0 := rfl

example : dividendStream 12 (1/20) 1 = 12 := by
  simp [dividendStream]

example : dividendStream 12 (1/20) 2 = 12 * (1 + 1/20) := by
  simp [dividendStream]

example : HasSum (discountedDividendStream 3 (1/2) (1/4)) 12 := by
  have h := dividendGordon_of_hasSumGrowing
    (hasSum_growingPerpetuity (3:ℝ) (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num))
  norm_num at h
  exact h


end MathlibExtTest.Economics.Finance.DividendGordon
