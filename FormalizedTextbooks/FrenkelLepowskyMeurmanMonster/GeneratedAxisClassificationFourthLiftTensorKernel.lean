/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpinKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSparseUnits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpatialTensor

/-! Sparse integer tensor coordinates of the actual normalized flag lift. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
-- The literal fiber product unfolds its actual normalizer projections.
/-- The sparse kernel is a coordinate of the genuine spin component of the local lift. -/
theorem generatedFourth_lift_normalized_spin_unit (v t : SpinIndex) :
    generatedFourthFlagNormalizedLift.val.1.val (Pi.single v 1) t =
      (generatedFourthLiftSpinKernel t v : ℝ) / 32 := by
  change monsterSourceY82Spin.val (generatedFourthFlagLiftSpin.val
    (xiSpinG (xiSpinGamma (monsterSourceY82Spin.val (Pi.single v 1))))) t = _
  exact generatedFourth_lift_spin_unit v t

private theorem spin_column_kernel (L : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (hunit : ∀ v t, L (Pi.single v 1) t = (generatedFourthLiftSpinKernel t v : ℝ) / 32)
    (i : Fin 24) (t : SpinIndex) :
    L
      (fun u => (griessConwayEncode generatedFourthAxis).2.2 u i) t =
        (∑ k : Fin 28, if i = generatedFourthQAffineTensorColumns k then
          ∑ s : Fin 4, (generatedFourthLiftUnitWeight k s : ℝ) *
            (generatedFourthLiftSpinKernel t (generatedFourthLiftSupportAddress k s) : ℝ)
          else 0) / (32 * Real.sqrt 2) := by
  classical
  rw [generatedFourth_lift_tensor_units, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    hunit]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i = generatedFourthQAffineTensorColumns k
  · simp only [h, ite_true]
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  · simp only [h, ite_false, zero_mul, Finset.sum_const_zero, zero_div]

/-- Original unit weights and the proved spin kernel give each transported tensor column. -/
theorem generatedFourth_lift_spin_column (i : Fin 24) (t : SpinIndex) :
    generatedFourthFlagNormalizedLift.val.1.val
      (fun u => (griessConwayEncode generatedFourthAxis).2.2 u i) t =
        (∑ k : Fin 28, if i = generatedFourthQAffineTensorColumns k then
          ∑ s : Fin 4, (generatedFourthLiftUnitWeight k s : ℝ) *
            (generatedFourthLiftSpinKernel t (generatedFourthLiftSupportAddress k s) : ℝ)
          else 0) / (32 * Real.sqrt 2) :=
  spin_column_kernel _ generatedFourth_lift_normalized_spin_unit i t

/-- The sparse integer numerator evaluates only genuine original coordinate units. -/
def generatedFourthLiftSparseTensorNumerator (t : SpinIndex) (i : Fin 24) : ℤ :=
  ∑ j : Fin 24, if generatedFourthLiftSpatialNumerator i j = 0 then 0 else
    generatedFourthLiftSpatialNumerator i j *
      ∑ k : Fin 28, if j = generatedFourthQAffineTensorColumns k then
        ∑ s : Fin 4, generatedFourthLiftUnitWeight k s *
          generatedFourthLiftSpinKernel t (generatedFourthLiftSupportAddress k s) else 0

/-- The actual normalized tensor has the exact sparse numerator with denominator sixty-four. -/
theorem generatedFourth_lift_tensor_kernel (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedFourthFlagNormalizedLift
      (griessConwayEncode generatedFourthAxis).2.2 t i =
        (generatedFourthLiftSparseTensorNumerator t i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedFourth_local_tensor_columns]
  simp_rw [generatedFourth_lift_spatial_numerator, generatedFourth_lift_spin_column]
  simp only [generatedFourthLiftSparseTensorNumerator, Int.cast_sum, Int.cast_ite,
    Int.cast_mul, Int.cast_zero]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : generatedFourthLiftSpatialNumerator i j = 0
  · simp only [h, ite_true, Int.cast_zero, zero_div, zero_mul]
  · simp only [h, ite_false]
    ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
