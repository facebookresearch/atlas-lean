/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorUnits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiSpinKernel

/-! Exact original tensor coordinates of the actual Q-corrected three-bases candidate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual fiber candidate, including the literal extraspecial central correction. -/
noncomputable def generatedFifthXiCorrectedFiber : localFiberSubgroup :=
  localFiberIncl generatedFifthXiCorrection * xiSpinLocalFiber

/-- The sparse integer numerator of the actual original three-bases tensor action. -/
def generatedFifthXiTensorNumerator (t : SpinIndex) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, if co1XiNumerator i j = 0 then 0 else
    co1XiNumerator i j * ∑ k : Fin 64,
      if j = (generatedFifthOddRootOutputData k).2 then
        ∑ b : ZMod 2, generatedFifthXiTensorWeight k b *
          generatedFifthXiSpinKernel t (generatedFifthXiTensorAddress k b) else 0

/-- The corrected numerator retains the actual translation, modulation and central sign. -/
def generatedFifthXiCorrectedTensorNumerator (t : SpinIndex) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (spinPhase generatedFifthXiCorrection t) *
    generatedFifthXiTensorNumerator (t + spinTranslation generatedFifthXiCorrection) i

/-- The physical Xi column entry is half its actual integral numerator. -/
theorem generatedFifth_xi_spatial_unit (i j : Fin 24) :
    xiSpinLocalFiber.val.2.val (Pi.single j 1) i = (co1XiNumerator i j : ℝ) / 2 := by
  change (co1XiMatrix *ᵥ Pi.single j 1) i = _
  simp [co1XiMatrix, co1XiMatrixQ]

/-- Each original spin column transforms through its exact signed coordinate-unit expansion. -/
theorem generatedFifth_xi_spin_column (i : Fin 24) (t : SpinIndex) :
    xiSpinHolomorph.val (fun u => (griessConwayEncode generatedFifthAxis).2.2 u i) t =
      (∑ k : Fin 64, if i = (generatedFifthOddRootOutputData k).2 then
        ∑ b : ZMod 2, (generatedFifthXiTensorWeight k b : ℝ) *
          (generatedFifthXiSpinKernel t (generatedFifthXiTensorAddress k b) : ℝ)
        else 0) / (8 * Real.sqrt 2) := by
  classical
  rw [generatedFifth_xi_tensor_units, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    generatedFifth_xi_spin_unit]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : i = (generatedFifthOddRootOutputData k).2
  · simp only [hi, ite_true]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp only [hi, ite_false, zero_mul, Finset.sum_const_zero, zero_div]

/-- The actual Xi tensor action has the certified integral numerator and original sqrt-two scale. -/
theorem generatedFifth_xi_tensor_coordinate (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation xiSpinLocalFiber
      (griessConwayEncode generatedFifthAxis).2.2 t i =
        (generatedFifthXiTensorNumerator t i : ℝ) / (16 * Real.sqrt 2) := by
  rw [generatedFourth_local_tensor_columns]
  simp_rw [generatedFifth_xi_spatial_unit]
  change (∑ j : Fin 24, (co1XiNumerator i j : ℝ) / 2 *
    xiSpinHolomorph.val (fun u => (griessConwayEncode generatedFifthAxis).2.2 u j) t) = _
  simp_rw [generatedFifth_xi_spin_column]
  simp only [generatedFifthXiTensorNumerator, Int.cast_sum, Int.cast_ite,
    Int.cast_zero, Int.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : co1XiNumerator i j = 0
  · simp only [hz, ite_true, Int.cast_zero, zero_div, zero_mul]
  · simp only [hz, ite_false]
    ring

/-- The full signed tensor coordinate belongs to the genuine corrected local fiber action. -/
theorem generatedFifth_xi_corrected_tensor_coordinate (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedFifthXiCorrectedFiber
      (griessConwayEncode generatedFifthAxis).2.2 t i =
        (generatedFifthXiCorrectedTensorNumerator t i : ℝ) / (16 * Real.sqrt 2) := by
  rw [generatedFifthXiCorrectedFiber, map_mul, LinearEquiv.mul_apply,
    generatedFourth_lift_q_tensor, generatedFifth_xi_tensor_coordinate]
  simp only [generatedFifthXiCorrectedTensorNumerator, Int.cast_mul,
    nortonUIntegerSign_real]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
