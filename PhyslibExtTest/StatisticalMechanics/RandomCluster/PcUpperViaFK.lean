/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PcUpperViaFK

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PcUpperViaFK`

Bernoulli bond percolation on `ℤ^d`:
* the headline `pc_nontrivial_of_two_le` at `d = 2` and `d = 3`, giving `0 < p_c(d) < 1`;
* `exists_theta_two_pos_below_one` with `pc_le_of_theta_pos`: some `p < 1` percolates on `ℤ²`,
  and `p_c(2) ≤ p`;
* `theta_two_le_theta_add`: `θ_2(p) ≤ θ_3(p)` (here at `p = 1/2`), and
  `pc_le_of_theta_pos` transports a percolating `p` from `ℤ²` to `ℤ³`;
* `theta_mono_parameter` at `1/4 ≤ 1/2`;
* `fkTheta_two_le_bernoulliTheta`: the wired FK–Ising percolation probability at `p = 1/2` is
  at most the Bernoulli one.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PcUpperViaFK

open scoped NNReal
open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Percolation

-- The headline on `ℤ²`: `0 < p_c(2) < 1`.
example : 0 < pc 2 ∧ pc 2 < 1 := pc_nontrivial_of_two_le (le_refl 2)

-- The headline on `ℤ³`.
example : 0 < pc 3 ∧ pc 3 < 1 := pc_nontrivial_of_two_le (by norm_num)

-- Some `p < 1` percolates on `ℤ²`, and `p_c(2)` lies below it.
example : ∃ p : ℝ≥0, p < 1 ∧ pc 2 ≤ p := by
  obtain ⟨p, hp1, hθ⟩ := exists_theta_two_pos_below_one
  exact ⟨p, hp1, pc_le_of_theta_pos p hp1.le hθ⟩

-- Percolation on the plane implies percolation on `ℤ³` at the same density.
example : theta 2 (1 / 2) (by norm_num) ≤ theta 3 (1 / 2) (by norm_num) :=
  theta_two_le_theta_add 1 (1 / 2) (by norm_num)

-- A density that percolates on `ℤ²` bounds `p_c(3)` from above.
example (p : ℝ≥0) (hp : p ≤ 1) (hθ : 0 < theta 2 p hp) : pc 3 ≤ p :=
  pc_le_of_theta_pos p hp (lt_of_lt_of_le hθ (theta_two_le_theta_add 1 p hp))

/-- `1/4 ≤ 1` in `ℝ≥0`. -/
theorem quarter_le_one : (1 / 4 : ℝ≥0) ≤ 1 := by
  rw [← NNReal.coe_le_coe]; norm_num

-- `θ_d(p)` is monotone in `p`.
example : theta 2 (1 / 4) quarter_le_one ≤ theta 2 (1 / 2) (by norm_num) :=
  theta_mono_parameter quarter_le_one (by norm_num) (by rw [← NNReal.coe_le_coe]; norm_num)

-- The wired FK–Ising percolation probability is at most the Bernoulli one (`p = 1/2`).
example : fkTheta 2 (p := ((1 / 2 : ℝ≥0) : ℝ)) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    ≤ theta 2 (1 / 2) (by norm_num) :=
  fkTheta_two_le_bernoulliTheta (1 / 2) (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PcUpperViaFK
