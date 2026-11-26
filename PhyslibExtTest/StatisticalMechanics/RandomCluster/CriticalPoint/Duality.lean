/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.Duality

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.Duality`

* `edgeProductCount` at `p = 1/2`, `m = 2`, `o = 1` is `1/4`;
* `dlt_dual_ratio_rel` and `dlt_edgeProduct_duality` at `p = 1/3`, `q = 2`;
* `dlt_self_duality_estimate` and `dlt_square_crossing_estimate` with a satisfiable dichotomy
  (`1/2 + 1/2 = 1`), and `dlt_dichotomy_lower_bound`;
* `dlt_rn_sandwich` with `c = 0` and equal weights on `Fin 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.Duality

open _root_.StatMech _root_.StatMech.BeffaraDC

-- The edge product of one open edge out of two at `p = 1/2`.
example : edgeProductCount (1 / 2) 2 1 = 1 / 4 := by norm_num [edgeProductCount]

-- The duality relation `(p / (1 - p)) (p* / (1 - p*)) = q` at `p = 1/3`, `q = 2`.
example : (1 / 3 / (1 - 1 / 3 : ℝ)) * (dualParam (1 / 3) 2 / (1 - dualParam (1 / 3) 2)) = 2 :=
  dlt_dual_ratio_rel (by norm_num) (by norm_num) (by norm_num)

-- Edge-product duality at `p = 1/3`, `q = 2`, `m = 3`, `o = 1`.
example := dlt_edgeProduct_duality (p := 1 / 3) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  3 1 (by norm_num)

-- The self-duality estimate at `q = 1` with connection probability `1/2`.
example : 1 / (1 + (1 : ℝ) ^ 2) ≤ 1 / 2 :=
  dlt_self_duality_estimate (dualConnectProb := 1 / 2) (by norm_num) (by norm_num)

-- The square-crossing estimate with `c = 1`.
example : 1 / (1 + (1 : ℝ)) ≤ 1 / 2 :=
  dlt_square_crossing_estimate (vertDualCross := 1 / 2) zero_le_one (by norm_num) (by norm_num)

-- The dichotomy lower bound with `x = 3/4`, `y = 1/4`, `Q = 1/3`.
example : 1 / (1 + 1 / 3 : ℝ) ≤ 3 / 4 :=
  dlt_dichotomy_lower_bound (y := 1 / 4) (by norm_num) (by norm_num) (by norm_num)

-- The RN sandwich with `c = 0` and constant weights.
example (A : Finset (Fin 2)) :
    (∑ _ω ∈ A, (1 : ℝ)) / (∑ _ω : Fin 2, (1 : ℝ))
      ≤ 1 ^ (2 * 0) * ((∑ _ω ∈ A, (1 : ℝ)) / (∑ _ω : Fin 2, (1 : ℝ))) :=
  dlt_rn_sandwich (fun _ => 1) (fun _ => 1) 1 le_rfl 0 (fun _ => one_pos) (fun _ => one_pos)
    (fun _ => by simp) (fun _ => by simp) A

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.Duality
