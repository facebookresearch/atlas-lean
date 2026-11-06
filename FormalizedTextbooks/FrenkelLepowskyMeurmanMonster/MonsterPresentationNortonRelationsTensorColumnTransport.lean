/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegralVector

/-! Whole actual local transport of tensor packets with arbitrary physical column rank. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every actual physical vector is its complete sum of coordinate columns. -/
theorem monsterNortonLeech_coordinate_sum (b : Fin 24 → ℝ) :
    (∑ j : Fin 24, b j • (Pi.single j 1 : Fin 24 → ℝ)) = b := by
  ext i
  simp [Pi.single_apply]

/-- Spatial transport of arbitrary tensor columns can be regrouped into actual output columns. -/
theorem monsterNortonTensor_column_regroup (a : Fin 24 → SpinSpace)
    (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) :
    (∑ i : Fin 24, monsterNortonTensorLift (conwayTensorCoordinates
      (a i ⊗ₜ[ℝ] e (Pi.single i 1)))) =
      ∑ j : Fin 24, monsterNortonTensorLift (conwayTensorCoordinates
        ((∑ i : Fin 24, e (Pi.single i 1) j • a i) ⊗ₜ[ℝ]
          (Pi.single j 1 : Fin 24 → ℝ))) := by
  conv_lhs =>
    arg 2
    ext i
    rw [← monsterNortonLeech_coordinate_sum (e (Pi.single i 1))]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
    TensorProduct.sum_tmul, TensorProduct.smul_tmul', map_sum]
  exact Finset.sum_comm

/-- The complete actual local operator transports every tensor column, without a rank-one input. -/
theorem monsterNortonLocal_tensor_columns_actual (f : localFiberSubgroup)
    (a : Fin 24 → SpinSpace) :
    localGriessRepresentation f
      (∑ i : Fin 24, monsterNortonTensorLift (conwayTensorCoordinates
        (a i ⊗ₜ[ℝ] (Pi.single i 1 : Fin 24 → ℝ)))) =
      ∑ j : Fin 24, monsterNortonTensorLift (conwayTensorCoordinates
        ((∑ i : Fin 24, f.val.2.val (Pi.single i 1) j • f.val.1.val (a i)) ⊗ₜ[ℝ]
          (Pi.single j 1 : Fin 24 → ℝ))) := by
  rw [map_sum]
  simp_rw [monsterNortonLocal_tensor_product_actual]
  exact monsterNortonTensor_column_regroup (fun i => f.val.1.val (a i)) f.val.2.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
