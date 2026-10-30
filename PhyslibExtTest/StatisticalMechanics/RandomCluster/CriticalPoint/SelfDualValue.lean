/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue`

* `dualParam` at small inputs: for Bernoulli percolation (`q = 1`) the dual of `p` is `1 - p`
  (`1/4 ↦ 3/4`); for `q = 2`, `1/3 ↦ 4/5`;
* `selfDualPoint` values: `p_sd(1) = 1/2` (Kesten's critical point of bond percolation on `ℤ²`)
  and `p_sd(4) = 2/3`;
* `dualParam_product_eq`, `selfDualPoint_is_fixed`, `selfDualPoint_mem_Ioo`, and
  `selfDualPoint_unique` at `q = 4`: `2/3` is the unique fixed point of `p ↦ p*`, and `1/2` is not
  a fixed point.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue

open _root_.StatMech _root_.StatMech.BeffaraDC

-- For `q = 1` the dual parameter is `1 - p`.
example : dualParam (1 / 4) 1 = 3 / 4 := by norm_num [dualParam]

-- For `q = 2`: `(1/3)* = (2/3 · 2) / (2/3 · 2 + 1/3) = 4/5`.
example : dualParam (1 / 3) 2 = 4 / 5 := by norm_num [dualParam]

/-- The self-dual point of bond percolation is `1/2`. -/
theorem selfDualPoint_one : selfDualPoint 1 = 1 / 2 := by
  norm_num [selfDualPoint]

/-- The self-dual point of the `q = 4` random-cluster model is `2/3`. -/
theorem selfDualPoint_four : selfDualPoint 4 = 2 / 3 := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [selfDualPoint, h]
  norm_num

-- The duality relation `p* p / ((1 - p*)(1 - p)) = q` at `p = 1/3`, `q = 2`.
example : dualParam (1 / 3) 2 * (1 / 3) / ((1 - dualParam (1 / 3) 2) * (1 - 1 / 3)) = 2 :=
  dualParam_product_eq (by norm_num) (by norm_num) (by norm_num)

-- `2/3` is fixed by the duality map at `q = 4`.
example : dualParam (2 / 3) 4 = 2 / 3 := by
  simpa [selfDualPoint_four] using selfDualPoint_is_fixed (q := 4) (by norm_num)

-- The self-dual point lies in `(0, 1)`.
example : selfDualPoint 4 ∈ Set.Ioo (0 : ℝ) 1 := selfDualPoint_mem_Ioo (by norm_num)

-- Uniqueness: a fixed point in `(0, 1)` at `q = 4` must be `2/3`.
example (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (h : dualParam p 4 = p) : p = 2 / 3 := by
  rw [← selfDualPoint_four]
  exact selfDualPoint_unique hp hp1 (by norm_num) h

-- `1/2` is not self-dual at `q = 4`, so uniqueness has content.
example : dualParam (1 / 2) 4 ≠ 1 / 2 := by norm_num [dualParam]

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualValue
