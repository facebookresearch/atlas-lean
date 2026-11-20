/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.Percolation.DctItem2
import Code.Percolation.SharpnessUnconditional
import Code.Sharpness.SharpnessBeta

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace StatMech

namespace Sharpness

open StatMech.Percolation StatMech.Lattice

variable {d : ℕ}












theorem sh1_tildePc_lt_one_of_pc_lt_one (hd : 0 < d) (hpc : pc d < 1) :
    (tildePc d : ℝ) < 1 := by
  have heq : tildePc d = pc d := (sharpness_unconditional hd).1
  rw [heq]
  exact_mod_cast hpc




theorem sh1_betaTildeC_pos_of_pc_lt_one {J : ℝ} (hJ : 0 < J) (hd : 0 < d)
    (hpc : pc d < 1) :
    0 < betaTildeC d J :=
  betaTildeC_pos hJ hd (sh1_tildePc_lt_one_of_pc_lt_one hd hpc)

























theorem sh1_theta_ge_betaForm_of_pc_lt_one {J β : ℝ} (hJ : 0 < J) (hd : 0 < d)
    (hpc : pc d < 1) (hβ : betaTildeC d J < β) :
    theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β)
      ≥ (β - betaTildeC d J) / β :=
  theta_ge_betaForm hJ hd (sh1_tildePc_lt_one_of_pc_lt_one hd hpc) hβ

end Sharpness

end StatMech
