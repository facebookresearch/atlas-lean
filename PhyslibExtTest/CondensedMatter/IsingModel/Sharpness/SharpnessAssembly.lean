/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessAssembly

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessAssembly`

* `sas_betaTildeC_lt_iff` and `sas_lt_betaTildeC_iff` applied under `p_c(d) < 1`;
* `sas_sharpness_betaForm`: the identity `p̃_c = p_c` and the mean-field bound extracted from it
  (conditional on `p_c(d) < 1`, discharged for `d ≥ 2` in `SharpnessBetaFormDimTwo`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SharpnessAssembly

open _root_.StatMech _root_.StatMech.Sharpness

-- Comparing `β` with `β̃_c` on both sides.
example (d : ℕ) (J β : ℝ) (hJ : 0 < J) (hd : 0 < d) (hpc : Percolation.pc d < 1) :
    (betaTildeC d J < β ↔ (Percolation.tildePc d : ℝ) < pBeta J β) ∧
      (β < betaTildeC d J ↔ pBeta J β < (Percolation.tildePc d : ℝ)) :=
  ⟨sas_betaTildeC_lt_iff hJ hd hpc, sas_lt_betaTildeC_iff hJ hd hpc⟩

-- `p̃_c = p_c` from the sharpness theorem.
example (d : ℕ) (hd : 0 < d) (hpc : Percolation.pc d < 1) :
    Percolation.tildePc d = Percolation.pc d :=
  (sas_sharpness_betaForm (J := 1) one_pos hd hpc).1

-- The mean-field bound from the sharpness theorem.
example (d : ℕ) (J β : ℝ) (hJ : 0 < J) (hd : 0 < d) (hpc : Percolation.pc d < 1)
    (hβ : betaTildeC d J < β) :
    Percolation.theta d (pBeta J β).toNNReal
      (pBeta_toNNReal_le_one _ _) ≥ (β - betaTildeC d J) / β :=
  (sas_sharpness_betaForm hJ hd hpc).2.2.2 β hβ

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SharpnessAssembly
