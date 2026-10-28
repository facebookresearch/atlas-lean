/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverMateCompactSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

/-! Genuine compact source fibers with the explicitly positive original spatial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

/-- Complete original Q agreement pairs the compact spin with the positive original spatial word. -/
theorem generatedRootEight_compact_positive_generator_compatibility (j : Fin 12)
    (h : generatedRootEightCompactSourceCondition (Fin.castAdd 2 j)) :
    spinBinaryAction (generatedRootEightCompactSpin (Fin.castAdd 2 j)) =
      leechBinaryAction (generatedRootEightGeneratorSpatial j) := by
  have hb := generatedRootEight_compact_source_compatibility (Fin.castAdd 2 j) h
  rw [generatedRootEight_compact_source_generator] at hb
  have hp := congrArg co1BinaryAction (generatedRootEight_generator_primitive_projection j)
  change leechBinaryAction (generatedRootEightGeneratorPrimitiveFiber j).val.2 =
    leechBinaryAction (generatedRootEightGeneratorSpatial j) at hp
  exact hb.trans hp

/-- The compact full-Q source paired with its genuine positive original isometry. -/
def generatedRootEightCompactPositiveGeneratorFiber (j : Fin 12)
    (h : generatedRootEightCompactSourceCondition (Fin.castAdd 2 j)) : localFiberSubgroup :=
  ⟨(generatedRootEightCompactSpin (Fin.castAdd 2 j), generatedRootEightGeneratorSpatial j),
    generatedRootEight_compact_positive_generator_compatibility j h⟩

/-- The whole actual local element of the explicitly positive source pair. -/
def generatedRootEightCompactPositiveGeneratorLocal (j : Fin 12)
    (h : generatedRootEightCompactSourceCondition (Fin.castAdd 2 j)) : H :=
  localFiberIntoH (generatedRootEightCompactPositiveGeneratorFiber j h)

/-- The positive source retains the original complete Conway projection. -/
theorem generatedRootEight_compact_positive_generator_projection (j : Fin 12)
    (h : generatedRootEightCompactSourceCondition (Fin.castAdd 2 j)) :
    projH (generatedRootEightCompactPositiveGeneratorLocal j h) =
      projH (generatedRootEightGeneratorPrimitiveLocal j) :=
  (generatedRootEight_generator_primitive_projection j).symm

/-- The genuine positive original point mover with its fully checked compact spin. -/
def generatedRootEightMoverPositiveFiber : localFiberSubgroup :=
  generatedRootEightCompactPositiveGeneratorFiber 10
    generatedRootEight_m22_compact_source_condition_10

/-- The genuine positive original mate word with its fully checked compact spin. -/
def generatedRootEightMatePositiveFiber : localFiberSubgroup :=
  generatedRootEightCompactPositiveGeneratorFiber 11
    generatedRootEight_m22_compact_source_condition_11

/-- The point mover retains the literal positive original spatial component. -/
theorem generatedRootEight_mover_positive_spatial :
    generatedRootEightMoverPositiveFiber.val.2 = leechNormSixHS100PointMover := by
  change generatedRootEightGeneratorSpatial 10 = _
  norm_num [generatedRootEightGeneratorSpatial]

/-- The mate retains the literal positive original spatial component. -/
theorem generatedRootEight_mate_positive_spatial :
    generatedRootEightMatePositiveFiber.val.2 = leechNormSixHS100MateOrientation := by
  change generatedRootEightGeneratorSpatial 11 = _
  norm_num [generatedRootEightGeneratorSpatial]

/-- The positive mover retains every original full-Q image and central phase. -/
theorem generatedRootEight_mover_positive_full_Q :
    spinConjugation generatedRootEightMoverPositiveFiber.val.1 =
      spinConjugation generatedRootEightPointMoverFiber.val.1 := by
  have h := generatedRootEight_m22_compact_source_condition_10
  change spinConjugation (generatedRootEightCompactSpin (Fin.castAdd 2 (10 : Fin 12))) =
    spinConjugation (generatedRootEightCompactSourceFiber (Fin.castAdd 2 (10 : Fin 12))).val.1 at h
  rw [generatedRootEight_compact_source_generator] at h
  exact h

/-- The positive mate retains every original full-Q image and central phase. -/
theorem generatedRootEight_mate_positive_full_Q :
    spinConjugation generatedRootEightMatePositiveFiber.val.1 =
      spinConjugation generatedRootEightMateFiber.val.1 := by
  have h := generatedRootEight_m22_compact_source_condition_11
  change spinConjugation (generatedRootEightCompactSpin (Fin.castAdd 2 (11 : Fin 12))) =
    spinConjugation (generatedRootEightCompactSourceFiber (Fin.castAdd 2 (11 : Fin 12))).val.1 at h
  rw [generatedRootEight_compact_source_generator] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
