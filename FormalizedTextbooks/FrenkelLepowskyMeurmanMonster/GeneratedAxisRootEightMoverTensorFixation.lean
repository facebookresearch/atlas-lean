/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorStartActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorFinishActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorAddress
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorHighPairCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorLowPairCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorFourierAddresses

/-! Unconditional complete tensor fixation by the genuine original corrected mover. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The genuine corrected mover spin carries the original eightfold source to the entire final tensor. -/
theorem generatedRootEight_mover_tensor_spin_source_actual (j : Fin 24) :
    generatedRootEightMoverCorrectedFiber.val.1.val
      ((8 : ℝ) • nortonUIntegerEmbed (fun n => generatedRootEightMoverTensorSourceInteger n j)) =
        nortonUIntegerEmbed (fun n => generatedRootEightMoverTensorFinalInteger n j) := by
  have h := generatedRootEight_mover_tensor_vector_replay j
    (fun n => generatedRootEightMoverTensorSourceInteger n j)
    generatedRootEight_mover_tensor_addresses generatedNinth_lower_spin_tensor_fourier_addresses
    (generatedRootEight_mover_tensor_start_actual j)
    (generatedRootEight_mover_tensor_pair_00 j)
    (generatedRootEight_mover_tensor_pair_01 j)
    (generatedRootEight_mover_tensor_pair_02 j)
  have he : generatedRootEightMoverTensorSpinOutput j =
      (fun n => generatedRootEightMoverTensorFinalInteger n j) := by
    funext n
    exact generatedRootEight_mover_tensor_finish_actual j n
  rw [he] at h
  exact h

/-- Every actual canonical spin column has its exact final signed integer coordinates. -/
theorem generatedRootEight_mover_tensor_spin_coordinate_actual (j : Fin 24) (t : SpinIndex) :
    generatedRootEightMoverCorrectedFiber.val.1.val
      (fun u => (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 u j) t =
        (generatedRootEightMoverTensorFinalInteger (nortonUIntegerLabel t) j : ℝ) /
          (128 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hin : (fun u => (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 u j) =
      (1 / (128 * Real.sqrt 2) : ℝ) •
        ((8 : ℝ) • nortonUIntegerEmbed (fun n => generatedRootEightMoverTensorSourceInteger n j)) := by
    funext u
    rw [generatedRootEight_canonical_tensor_raw_actual,
      ← generatedRootEight_mover_tensor_source_actual]
    simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
    field_simp [hs]
    ring
  rw [hin, map_smul, generatedRootEight_mover_tensor_spin_source_actual]
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, one_div]
  ring

/-- The actual corrected mover retains the entire original positive spatial component. -/
theorem generatedRootEight_mover_tensor_spatial : generatedRootEightMoverCorrectedFiber.val.2 =
    leechNormSixHS100PointMover := by
  change generatedFourthMonomialSpatialProjection generatedRootEightMoverCorrectedFiber = _
  rw [generatedRootEightMoverCorrectedFiber, map_mul]
  change (1 : leechIsomSubgroup) * generatedRootEightMoverPositiveFiber.val.2 = _
  rw [one_mul, generatedRootEight_mover_positive_spatial]

/-- The whole actual canonical tensor is fixed by the genuine corrected mover, including every zero. -/
theorem generatedRootEight_mover_corrected_canonical_tensor (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedRootEightMoverCorrectedFiber
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i := by
  rw [generatedAxisGlobalTensor_local_coordinate]
  simp_rw [generatedRootEight_mover_tensor_spin_coordinate_actual,
    generatedRootEight_mover_tensor_spatial]
  change (∑ j : Fin 24,
    (generatedRootEightMoverTensorFinalInteger (nortonUIntegerLabel t) j : ℝ) /
      (128 * Real.sqrt 2) * leechIsomMatrix leechNormSixHS100PointMover i j) = _
  calc
    _ = ∑ j : Fin 24, leechIsomMatrix leechNormSixHS100PointMover i j *
        ((generatedRootEightMoverTensorFinalInteger (nortonUIntegerLabel t) j : ℝ) /
          (128 * Real.sqrt 2)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = _ := generatedRootEight_mover_tensor_spatial_actual t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
