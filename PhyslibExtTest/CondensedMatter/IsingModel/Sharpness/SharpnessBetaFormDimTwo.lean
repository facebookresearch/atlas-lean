/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBetaFormDimTwo

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.SharpnessBetaFormDimTwo`

* `theta_ge_betaForm_of_two_le` and `theta_ge_betaForm_of_two_le_closed` on `ℤ²` with `J = 1`;
* `sharpness_betaForm_of_two_le` on `ℤ³` with `J = 1`: its first conjunct `p̃_c = p_c`, and the
  equivalence `β > β̃_c ↔ p(β) > p̃_c`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SharpnessBetaFormDimTwo

open _root_.StatMech _root_.StatMech.Sharpness

-- The mean-field lower bound on `θ` above `β̃_c`, on `ℤ²`.
example (β : ℝ) (hβ : betaTildeC 2 1 < β) :
    Percolation.theta 2 (pBeta 1 β).toNNReal
      (pBeta_toNNReal_le_one _ _) ≥ (β - betaTildeC 2 1) / β :=
  theta_ge_betaForm_of_two_le le_rfl one_pos hβ

-- The closed form at `β = β̃_c`: `θ ≥ 0`.
example : Percolation.theta 2 (pBeta 1 (betaTildeC 2 1)).toNNReal
      (pBeta_toNNReal_le_one _ _) ≥
    (betaTildeC 2 1 - betaTildeC 2 1) / betaTildeC 2 1 :=
  theta_ge_betaForm_of_two_le_closed le_rfl one_pos le_rfl

-- `p̃_c = p_c` on `ℤ³`.
example : Percolation.tildePc 3 = Percolation.pc 3 :=
  (sharpness_betaForm_of_two_le (d := 3) (J := 1) (by norm_num) one_pos).1

-- Comparing `β` with `β̃_c` is comparing `p(β)` with `p̃_c`.
example (β : ℝ) : betaTildeC 3 1 < β ↔ (Percolation.tildePc 3 : ℝ) < pBeta 1 β :=
  (sharpness_betaForm_of_two_le (d := 3) (J := 1) (by norm_num) one_pos).2.1 β

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.SharpnessBetaFormDimTwo
