/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedSpatialCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorSourceActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverTensorVectorReplay

/-! Actual positive spatial tensor compatibility from every original signed integer coordinate. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual positive spatial matrix carries the complete spin-output tensor to the original source. -/
theorem generatedRootEight_mover_tensor_spatial_real (n : Fin 4096) (i : Fin 24) :
    (∑ j : Fin 24, leechIsomMatrix leechNormSixHS100PointMover i j *
      ((generatedRootEightMoverTensorFinalInteger n j : ℝ) / (128 * Real.sqrt 2))) =
        (generatedRootEightMoverTensorSourceInteger n i : ℝ) / (16 * Real.sqrt 2) := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have he : ∀ j : Fin 24, leechIsomMatrix leechNormSixHS100PointMover i j *
      ((generatedRootEightMoverTensorFinalInteger n j : ℝ) / (128 * Real.sqrt 2)) =
        ((generatedRootEightMoverSpatialNumerator i j *
          generatedRootEightMoverTensorFinalInteger n j : ℤ) : ℝ) / (1024 * Real.sqrt 2) := by
    intro j
    rw [generatedRootEight_mover_spatial_matrix]
    push_cast
    field_simp [hs] <;> ring
  simp_rw [he]
  rw [← Finset.sum_div, ← Int.cast_sum, generatedRootEight_mover_tensor_spatial_integer]
  push_cast
  field_simp [hs] <;> ring

/-- Every actual canonical tensor coordinate is recovered by the genuine positive spatial mover. -/
theorem generatedRootEight_mover_tensor_spatial_actual (t : SpinIndex) (i : Fin 24) :
    (∑ j : Fin 24, leechIsomMatrix leechNormSixHS100PointMover i j *
      ((generatedRootEightMoverTensorFinalInteger (nortonUIntegerLabel t) j : ℝ) /
        (128 * Real.sqrt 2))) =
          (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.2 t i := by
  rw [generatedRootEight_canonical_tensor_raw_actual,
    ← generatedRootEight_mover_tensor_source_actual]
  exact generatedRootEight_mover_tensor_spatial_real _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
