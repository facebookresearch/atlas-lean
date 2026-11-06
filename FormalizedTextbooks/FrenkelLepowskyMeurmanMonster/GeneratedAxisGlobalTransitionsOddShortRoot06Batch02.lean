/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMaskEncode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache06

/-! Complete original preferred-Q certificates for odd root 6, packet batch 2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full original binary output masks against the actual preferred coordinate formula.
set_option maxRecDepth 10000 in
/-- Every complete candidate binary image is the actual source output vector. -/
theorem generatedAxisGlobalOddShortRoot06Batch02_vector (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddRootQCacheBinary 6)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).2).base)) =
      generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalShortQFinite
        (generatedAxisGlobalOddShortRootLabels 6
          (generatedAxisGlobalOddShortBatchNumber 2 i))).base) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 full original central phases with the actual canonical triangular cocycle.
set_option maxRecDepth 10000 in
/-- Every candidate central bit is the complete original source output phase. -/
theorem generatedAxisGlobalOddShortRoot06Batch02_central (i : Fin 256) :
    (if Nat.testBit (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddRootMaskRows 6)
      (generatedAxisGlobalOddRootMaskCoefficients 6)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).2).base))) 0
      then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddShortRootPhases 6 (generatedAxisGlobalOddShortBatchNumber 2 i) := by
  revert i
  decide +kernel

/-- Both finite certificates give the complete actual signed preferred-Q image. -/
theorem generatedAxisGlobalOddShortRoot06Batch02_QImage (i : Fin 256) :
    generatedAxisGlobalOddRootQFast 6 (generatedAxisGlobalPairQFinite
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).1
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 2 i)).2) =
      qCentral (generatedAxisGlobalOddShortRootPhases 6
        (generatedAxisGlobalOddShortBatchNumber 2 i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels 6
          (generatedAxisGlobalOddShortBatchNumber 2 i)) :=
  generatedAxisGlobalOddRootMaskCheck_actual 6
    generatedAxisGlobalOddRootQCache06_certificate _ _ _ rfl
    (generatedAxisGlobalShortQFinite_positive _)
    (generatedAxisGlobalOddShortRoot06Batch02_vector i)
    (generatedAxisGlobalOddShortRoot06Batch02_central i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
