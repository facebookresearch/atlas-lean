/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpinNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm

/-! Ordinary spatial columns and exact integer matrix coordinates of the actual flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual transported tensor representation is ordinary spin-by-spatial column action. -/
theorem generatedFourth_local_tensor_columns (f : localFiberSubgroup)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation f T t i = ∑ j : Fin 24,
      f.val.2.val (Pi.single j 1) i * f.val.1.val (fun u => T u j) t := by
  obtain ⟨v, rfl⟩ := conwayTensorCoordinates.surjective T
  rw [localTensorRepresentation_coordinates]
  induction v using TensorProduct.inductionOn with
  | tmul a b =>
    change conwayTensorCoordinates (TensorProduct.congr _ _ (a ⊗ₜ[ℝ] b)) t i = _
    rw [TensorProduct.congr_tmul, conwayTensorCoordinates_tmul]
    simp only [conwayTensorCoordinates_tmul]
    have hcol (j : Fin 24) : (fun u => a u * b j) = b j • a := by
      funext u
      exact mul_comm _ _
    simp_rw [hcol, map_smul]
    change f.val.1.val a t * f.val.2.val b i =
      ∑ j, f.val.2.val (Pi.single j 1) i * (b j * f.val.1.val a t)
    have hb : b = ∑ j : Fin 24, b j • (Pi.single j 1 : Fin 24 → ℝ) := by
      funext k
      simp [Pi.single_apply]
    have hbe := congrArg (fun x => f.val.2.val x i) hb
    simp only [map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul] at hbe
    rw [hbe]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  | add a b ha hb =>
    have hcol (j : Fin 24) :
        (fun u => conwayTensorCoordinates a u j + conwayTensorCoordinates b u j) =
          (fun u => conwayTensorCoordinates a u j) +
            (fun u => conwayTensorCoordinates b u j) := rfl
    simp only [map_add, Pi.add_apply, ha, hb]
    simp_rw [hcol, map_add, Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]

/-- The original matrix numerator is twice the actual physical column entry. -/
theorem generatedFourth_lift_spatial_numerator (i j : Fin 24) :
    generatedFourthFlagNormalizedLift.val.2.val (Pi.single j 1) i =
      (generatedFourthLiftSpatialNumerator i j : ℝ) / 2 := by
  change qSign (monsterSourceY82SignCode.val i) *
    (co1XiMatrix *ᵥ (fun k => qSign (monsterSourceY82SignCode.val k) *
      (Pi.single j 1 : Fin 24 → ℝ) k)) (generatedFourthFlagCorrectionCoordinates i) = _
  rw [co1XiMatrix_half_numerator, Matrix.smul_mulVec]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Matrix.map_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Pi.smul_apply, smul_eq_mul, generatedFourthLiftSpatialNumerator,
    Int.cast_mul, generatedFourth_lift_int_sign_real]
  have hcast (n : ℤ) : (Int.castRingHom ℝ) n = (n : ℝ) := rfl
  simp only [hcast]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
