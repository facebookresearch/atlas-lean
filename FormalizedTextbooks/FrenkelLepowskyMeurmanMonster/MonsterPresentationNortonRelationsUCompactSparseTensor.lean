/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A finite actual Griess-vector expansion for Norton transport of a physical delta column. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- The genuine linear inclusion of physical tensor coordinates in the Griess space. -/
noncomputable def monsterNortonTensorLift :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] GriessSpace :=
  generatedCentralMinus.subtype.comp generatedCentralMinusTensorEquiv.symm.toLinearMap

/-- This linear inclusion is exactly the actual Conway decoder on pure tensor coordinates. -/
theorem monsterNortonTensorLift_apply (T : SpinIndex → Fin 24 → ℝ) :
    monsterNortonTensorLift T = griessConwayDecode (0, (0, T)) := rfl

/-- With a fixed physical vector, a pure tensor is linear in its spin coordinate. -/
noncomputable def monsterNortonTensorRankOne (b : Fin 24 → ℝ) : SpinSpace →ₗ[ℝ] GriessSpace :=
  { toFun := fun a => monsterNortonTensorLift (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))
    map_add' := by
      intro a c
      rw [TensorProduct.add_tmul, map_add, map_add]
    map_smul' := by
      intro c a
      rw [← TensorProduct.smul_tmul', map_smul, map_smul]
      rfl }

/-- The rank-one map uses the actual physical tensor coordinates. -/
theorem monsterNortonTensorRankOne_apply (b : Fin 24 → ℝ) (a : SpinSpace) :
    monsterNortonTensorRankOne b a =
      griessConwayDecode (0, (0, conwayTensorCoordinates (a ⊗ₜ[ℝ] b))) :=
  monsterNortonTensorLift_apply _

private theorem rank_one_columns (a : SpinSpace) (b : Fin 24 → ℝ) :
    monsterNortonTensorRankOne b a =
      ∑ i : Fin 24, b i • monsterNortonTensorLift (conwaySpinColumn a i) := by
  have hc : conwayTensorCoordinates (a ⊗ₜ[ℝ] b) =
      ∑ i : Fin 24, b i • conwaySpinColumn a i := by
    ext t j
    simp only [conwayTensorCoordinates_tmul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, conwaySpinColumn]
    simp only [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    exact mul_comm (a t) (b j)
  change monsterNortonTensorLift (conwayTensorCoordinates (a ⊗ₜ[ℝ] b)) = _
  rw [hc, map_sum]
  simp only [map_smul]

private theorem local_pure_tensor (f : localFiberSubgroup) (T : SpinIndex → Fin 24 → ℝ) :
    localGriessRepresentation f (monsterNortonTensorLift T) =
      monsterNortonTensorLift (localTensorRepresentation f T) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [monsterNortonTensorLift_apply, localGriessRepresentation_encode,
    griessConwayEncode_decode _ (by intros; rfl), monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl)]
  rw [localConwayRawRepresentation_apply]
  simp only [map_zero]

private theorem local_tensor_column (f : localFiberSubgroup) (a : SpinSpace) (j : Fin 24) :
    localGriessRepresentation f (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorRankOne (f.val.2.val (Pi.single j 1)) (f.val.1.val a) := by
  rw [local_pure_tensor]
  have hc : conwaySpinColumn a j =
      conwayTensorCoordinates (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
    ext t i
    simp only [conwaySpinColumn, conwayTensorCoordinates_tmul, Pi.single_apply]
    by_cases h : i = j <;> simp [h]
  rw [hc, localTensorRepresentation_coordinates]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (TensorProduct.congr f.val.1.val f.val.2.val
      (a ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)))) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-- The actual Norton image is a finite sum of genuine physical spin-delta tensor columns. -/
theorem monsterNortonUCompactSparseTensor (u : SpinIndex) (j : Fin 24) :
    y555NortonActualU.val (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j)) =
      (1 / 8 : ℝ) • ∑ a : XiGrayIndex,
        (monsterNortonUCompactBasisSign u a : ℝ) •
          ∑ i : Fin 24, monsterNortonUFiber.val.2.val (Pi.single j 1) i •
            monsterNortonTensorLift (conwaySpinColumn
              (Pi.single (monsterNortonUCompactBasisIndex u a) 1) i) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwaySpinColumn (Pi.single u 1) j)) = _
  rw [local_tensor_column, monsterNortonUCompactSpin_actual_basis, map_smul, map_sum]
  simp only [map_smul, rank_one_columns]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
