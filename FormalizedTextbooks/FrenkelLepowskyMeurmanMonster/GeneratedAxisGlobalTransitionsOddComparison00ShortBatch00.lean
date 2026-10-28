/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonMaskAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonShortData

/-! Check a complete original preferred-short batch of the actual phase-correct comparison. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full original binary output masks against the actual preferred coordinate formula.
set_option maxRecDepth 10000 in
/-- Every complete candidate binary image is the actual source output vector. -/
theorem generatedAxisGlobalOddComparison00ShortBatch00_vector (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddComparisonQCacheBinary 0)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2).base)) =
      generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalShortQFinite
        (generatedAxisGlobalOddComparisonShortLabels 0
          (generatedAxisGlobalOddShortBatchNumber 0 i))).base) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 full original central phases with the actual canonical triangular cocycle.
set_option maxRecDepth 10000 in
/-- Every candidate central bit is the complete original source output phase. -/
theorem generatedAxisGlobalOddComparison00ShortBatch00_central (i : Fin 256) :
    (if Nat.testBit (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddComparisonMaskRows 0)
      (generatedAxisGlobalOddComparisonMaskCoefficients 0)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2).base))) 0
      then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddComparisonShortPhases 0 (generatedAxisGlobalOddShortBatchNumber 0 i) :=
    by
  revert i
  decide +kernel

/-- Both finite certificates give the complete actual signed preferred-Q image. -/
theorem generatedAxisGlobalOddComparison00ShortBatch00_QImage (i : Fin 256) :
    generatedAxisGlobalOddComparisonQImage 0 (generatedAxisGlobalPairQFinite
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2) =
      qCentral (generatedAxisGlobalOddComparisonShortPhases 0
        (generatedAxisGlobalOddShortBatchNumber 0 i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddComparisonShortLabels 0
          (generatedAxisGlobalOddShortBatchNumber 0 i)) :=
  generatedAxisGlobalOddComparisonMaskCheck_actual 0 _ _ _ rfl
    (generatedAxisGlobalShortQFinite_positive _)
    (generatedAxisGlobalOddComparison00ShortBatch00_vector i)
    (generatedAxisGlobalOddComparison00ShortBatch00_central i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
