/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneIntegerSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Full tensor-column transport and the exact corrected Xi integer numerator. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct
set_option backward.isDefEq.respectTransparency true

/-- Each tensor coordinate is transported by the actual spin operator and spatial matrix. -/
theorem generatedSeventhXi_tensor_column_action (f : localFiberSubgroup)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f T t i =
      ∑ j : Fin 24, f.val.1.val (fun u => T u j) t * f.val.2.val (Pi.single j 1) i := by
  have hc : T = ∑ j : Fin 24, conwayTensorCoordinates
      ((fun u => T u j) ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ)) := by
    funext u k
    simp only [Finset.sum_apply, conwayTensorCoordinates_tmul, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
  have hcol (j : Fin 24) : localTensorRepresentation f
      (conwayTensorCoordinates ((fun u => T u j) ⊗ₜ[ℝ]
        (Pi.single j 1 : Fin 24 → ℝ))) =
      (fun u k => f.val.1.val (fun v => T v j) u * f.val.2.val (Pi.single j 1) k) := by
    rw [localTensorRepresentation_coordinates]
    change conwayTensorCoordinates (TensorProduct.congr f.val.1.val f.val.2.val
      ((fun u => T u j) ⊗ₜ[ℝ] (Pi.single j 1 : Fin 24 → ℝ))) = _
    rw [TensorProduct.congr_tmul]
    funext u k
    exact conwayTensorCoordinates_tmul _ _ _ _
  conv_lhs => rw [hc, map_sum]
  simp_rw [hcol]
  simp only [Finset.sum_apply]

/-- The spatial numerator exposed as an ordinary coordinate function. -/
def generatedSeventhXiPlaneTensorSpatialNumerator (i j : Fin 24) : ℤ :=
  generatedSeventhXiPlaneMatrixNumerator i j

/-- The full integral tensor numerator sums all twenty-four columns after the original Gaussian. -/
def generatedSeventhXiPlaneIntegerTensor (v : Fin 4096 → Fin 24 → ℤ) :
    Fin 4096 → Fin 24 → ℤ := fun d i =>
  ∑ j : Fin 24, generatedSeventhXiPlaneTensorSpatialNumerator i j *
    generatedSeventhXiPlaneIntegerSpin (fun k => v k j) d

/-- Dividing this full numerator by sixteen is the actual corrected local tensor action. -/
theorem generatedSeventhXiPlane_integer_tensor_embed (v : Fin 4096 → Fin 24 → ℤ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedSeventhXiPlaneFiber
      (fun u j => (v (nortonUIntegerLabel u) j : ℝ)) t i =
        (generatedSeventhXiPlaneIntegerTensor v (nortonUIntegerLabel t) i : ℝ) / 16 := by
  rw [generatedSeventhXi_tensor_column_action]
  simp only [generatedSeventhXiPlaneIntegerTensor, Int.cast_sum, Int.cast_mul,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrFun (generatedSeventhXiPlane_integer_spin_embed (fun d => v d j)) t
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed] at hs
  have he : (fun u => (v (nortonUIntegerLabel u) j : ℝ)) =
      nortonUIntegerEmbed (fun d => v d j) := rfl
  rw [he, hs]
  have hm : generatedSeventhXiPlaneFiber.val.2.val (Pi.single j 1) i =
      (generatedSeventhXiPlaneTensorSpatialNumerator i j : ℝ) / 2 :=
    generatedSeventhXiPlaneFiber_matrix_coordinate i j
  rw [hm]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
