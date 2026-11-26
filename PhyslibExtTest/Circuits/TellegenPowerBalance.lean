/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Circuits.TellegenPowerBalance
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix
open PhyslibExt.Circuits.TellegenPowerBalance

namespace PhyslibExtTest.Circuits.TellegenPowerBalance

/-- Head-positive incidence of one branch from node `0` to node `1`:
potentials `3` and `1` give branch voltage `-2`, branch current `5` gives
injections `-5` and `5`, and both powers are `-10`. -/
example : (![-2] : Fin 1 → ℝ) ⬝ᵥ (![5] : Fin 1 → ℝ) =
    (![3, 1] : Fin 2 → ℝ) ⬝ᵥ (![-5, 5] : Fin 2 → ℝ) :=
  branchPower_eq_nodePower (!![-1; 1] : Matrix (Fin 2) (Fin 1) ℝ) ![3, 1] ![-5, 5]
    ![-2] ![5]
    (by
      ext e
      fin_cases e
      norm_num [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two])
    (by
      ext n
      fin_cases n <;> norm_num [Matrix.mulVec, dotProduct])

/-- The same balance with the tail-positive sign convention: the theorem
places no sign convention on the matrix. -/
example : (![2] : Fin 1 → ℝ) ⬝ᵥ (![5] : Fin 1 → ℝ) =
    (![3, 1] : Fin 2 → ℝ) ⬝ᵥ (![5, -5] : Fin 2 → ℝ) :=
  branchPower_eq_nodePower (!![1; -1] : Matrix (Fin 2) (Fin 1) ℝ) ![3, 1] ![5, -5]
    ![2] ![5]
    (by
      ext e
      fin_cases e
      norm_num [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two])
    (by
      ext n
      fin_cases n <;> norm_num [Matrix.mulVec, dotProduct])

end PhyslibExtTest.Circuits.TellegenPowerBalance
