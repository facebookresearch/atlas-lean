/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc`

The FK–Ising model (`q = 2`) on `ℤ²`:
* `tzp_fkTheta_monotone_in_p`: `θ¹(1/4, 2) ≤ θ¹(1/2, 2)`;
* the headline `tzp_fkTheta_eq_zero_of_lt_pc` with the witness `p = 1/16`: its hypothesis
  `p < p_c(2, 2)` is discharged from `p_c(2, 2) ≥ 1/8` (`fkTheta_eq_zero_of_lt` and
  `le_fkPc_of_mem` from `PcNontrivial`), and it yields `θ¹(1/16, 2) = 0`.

Not tested: `tzp_fkTheta_eq_zero_of_le_pc_of_pc`, whose hypothesis `θ¹(p_c, 2) = 0` (continuity at
criticality) is not proved in the library.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc

open _root_.StatMech _root_.StatMech.FK

-- `θ¹(p, 2)` is monotone in `p` on `ℤ²`.
example : fkTheta 2 (p := 1 / 4) (q := 2) (by norm_num) (by norm_num) (by norm_num)
    ≤ fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) :=
  tzp_fkTheta_monotone_in_p (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `p_c(2, 2) ≥ 1/8`, from the path-counting bound at `p = 1/8`. -/
theorem eighth_le_fkPc : (1 / 8 : ℝ) ≤ fkPc 2 2 :=
  le_fkPc_of_mem ⟨by norm_num, by norm_num, by norm_num,
    fkTheta_eq_zero_of_lt (d := 2) (by norm_num) (p := 1 / 8) (q := 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩

-- The headline with a discharged hypothesis: `1/16 < p_c(2, 2)`, so `θ¹(1/16, 2) = 0`.
example : fkTheta 2 (p := 1 / 16) (q := 2) (by norm_num) (by norm_num) (by norm_num) = 0 :=
  tzp_fkTheta_eq_zero_of_lt_pc (by norm_num) (by norm_num)
    (lt_of_lt_of_le (by norm_num) eighth_le_fkPc)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc
