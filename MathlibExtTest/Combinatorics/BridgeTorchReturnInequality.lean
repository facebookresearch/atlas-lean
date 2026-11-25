/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.BridgeTorchReturnInequality

open MetaMathlibExt.BridgeTorchGeneralizations

private def returnMargin (R : Finset ℕ) (hR : R.Nonempty) : ℚ :=
  9 / 2 * ((R.card : ℚ) - 1) + ((R.max' hR : ℕ) : ℚ) +
    ∑ i ∈ R, (bridgeWeight i - (i : ℚ))

-- A single returner with weight zero attains the bound.
example : returnMargin ({1} : Finset ℕ) (by decide) = 0 := by
  norm_num [returnMargin, bridgeWeight]

-- At two returners the maximum may use the affine formula for the weights.
example : returnMargin ({2, 7} : Finset ℕ) (by decide) = 55 / 6 := by
  norm_num [returnMargin, bridgeWeight, Finset.sum_insert]
example : 0 ≤ returnMargin ({2, 7} : Finset ℕ) (by decide) :=
  bridgeWeight_return_inequality (R := {2, 7}) (hR := by decide)
    (hR3 := by decide) (hpos := by decide)

-- All three smallest weights vanish, but the return margin is positive.
example : returnMargin ({1, 2, 3} : Finset ℕ) (by decide) = 6 := by
  norm_num [returnMargin, bridgeWeight, Finset.sum_insert]
example : 0 ≤ returnMargin ({1, 2, 3} : Finset ℕ) (by decide) :=
  bridgeWeight_return_inequality (R := {1, 2, 3}) (hR := by decide)
    (hR3 := by decide) (hpos := by decide)
