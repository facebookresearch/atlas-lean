/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildePcBetaForm

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildePcBetaForm`

* `sh1_tildePc_lt_one_of_pc_lt_one`, `sh1_betaTildeC_pos_of_pc_lt_one` and
  `sh1_theta_ge_betaForm_of_pc_lt_one` applied under `p_c(d) < 1` (conditional form; the
  hypothesis is discharged for `d ≥ 2` downstream, in `SharpnessBetaFormDimTwo`);
* together: `p̃_c < 1` and `β̃_c > 0` at once.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.TildePcBetaForm

open _root_.StatMech _root_.StatMech.Sharpness

-- `p_c < 1` gives `p̃_c < 1` and `β̃_c > 0`.
example (d : ℕ) (hd : 0 < d) (hpc : Percolation.pc d < 1) :
    (Percolation.tildePc d : ℝ) < 1 ∧ 0 < betaTildeC d 1 :=
  ⟨sh1_tildePc_lt_one_of_pc_lt_one hd hpc, sh1_betaTildeC_pos_of_pc_lt_one one_pos hd hpc⟩

-- The mean-field bound on `θ` above `β̃_c`.
example (d : ℕ) (J β : ℝ) (hJ : 0 < J) (hd : 0 < d) (hpc : Percolation.pc d < 1)
    (hβ : betaTildeC d J < β) :
    Percolation.theta d (pBeta J β).toNNReal
      (pBeta_toNNReal_le_one _ _) ≥ (β - betaTildeC d J) / β :=
  sh1_theta_ge_betaForm_of_pc_lt_one hJ hd hpc hβ

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.TildePcBetaForm
