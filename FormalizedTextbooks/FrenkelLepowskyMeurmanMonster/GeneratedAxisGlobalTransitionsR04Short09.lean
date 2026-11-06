/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortIndexedMask
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR04Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache04

/-! Complete original root-4 preferred-Q transport for packet batch9. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot04Short09_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 4)
      (generatedAxisGlobalFifthInputMaskData 9 i) =
      generatedAxisGlobalShortIndexedMask (generatedAxisGlobalFifthRoot04ShortLabelData 9 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot04Short09_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 4)
      (generatedAxisGlobalFifthMaskCoefficients 4)
      (generatedAxisGlobalFifthInputMaskData 9 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot04ShortPhaseData 9 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-4 Q image. -/
theorem generatedAxisGlobalFifthRoot04Short09_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 4 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 9 i))) =
      qCentral (generatedAxisGlobalFifthRoot04ShortPhaseData 9 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot04ShortLabelData 9 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 4 generatedAxisGlobalFifthQCache04_actual,
    generatedAxisGlobalShortIndexedMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot04Short09_vector_checked i)
    (generatedAxisGlobalFifthRoot04Short09_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
