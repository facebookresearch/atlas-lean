/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BinPacking

/-- Boundary check: the bound instantiates for three items packed
feasibly into one bin, giving `nextFit ≤ 2`. -/
example {sizes : List ℝ} (hpos : ∀ x ∈ sizes, 0 < x) (hle : ∀ x ∈ sizes, x ≤ 1)
    {a : ℕ → ℕ} (hfeas : FeasibleAssignment sizes 1 a)
    (hcov : ∀ i, i < sizes.length → a i < 1) :
    nextFitBins sizes ≤ 2 * 1 :=
  nextFit_le_two_mul_opt hpos hle hfeas hcov

/-- The empty list needs no bins: its Next Fit count is `0` by the
defining equation. -/
example : nextFitBins [] = 0 := rfl
