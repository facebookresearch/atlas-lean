/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortRootData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMaskEncode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache04

/-! Complete original preferred-Q certificates for odd root 4, packet batch 0. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full original binary output masks against the actual preferred coordinate formula.
set_option maxRecDepth 10000 in
/-- Every complete candidate binary image is the actual source output vector. -/
theorem generatedAxisGlobalOddShortRoot04Batch00_vector (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalOddRootQCacheBinary 4)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2).base)) =
      generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalShortQFinite
        (generatedAxisGlobalOddShortRootLabels 4
          (generatedAxisGlobalOddShortBatchNumber 0 i))).base) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 full original central phases with the actual canonical triangular cocycle.
set_option maxRecDepth 10000 in
/-- Every candidate central bit is the complete original source output phase. -/
theorem generatedAxisGlobalOddShortRoot04Batch00_central (i : Fin 256) :
    (if Nat.testBit (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddRootMaskRows 4)
      (generatedAxisGlobalOddRootMaskCoefficients 4)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalPairQFinite
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
        (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2).base))) 0
      then (1 : ZMod 2) else 0) =
      generatedAxisGlobalOddShortRootPhases 4 (generatedAxisGlobalOddShortBatchNumber 0 i) := by
  revert i
  decide +kernel

/-- Both finite certificates give the complete actual signed preferred-Q image. -/
theorem generatedAxisGlobalOddShortRoot04Batch00_QImage (i : Fin 256) :
    generatedAxisGlobalOddRootQFast 4 (generatedAxisGlobalPairQFinite
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).1
      (generatedAxisGlobalOddShortInput (generatedAxisGlobalOddShortBatchNumber 0 i)).2) =
      qCentral (generatedAxisGlobalOddShortRootPhases 4
        (generatedAxisGlobalOddShortBatchNumber 0 i)) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalOddShortRootLabels 4
          (generatedAxisGlobalOddShortBatchNumber 0 i)) :=
  generatedAxisGlobalOddRootMaskCheck_actual 4
    generatedAxisGlobalOddRootQCache04_certificate _ _ _ rfl
    (generatedAxisGlobalShortQFinite_positive _)
    (generatedAxisGlobalOddShortRoot04Batch00_vector i)
    (generatedAxisGlobalOddShortRoot04Batch00_central i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
