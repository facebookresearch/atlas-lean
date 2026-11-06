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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR06Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache06

/-! Complete original root-6 preferred-Q transport for packet batch8. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot06Short08_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 6)
      (generatedAxisGlobalFifthInputMaskData 8 i) =
      generatedAxisGlobalShortIndexedMask (generatedAxisGlobalFifthRoot06ShortLabelData 8 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot06Short08_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 6)
      (generatedAxisGlobalFifthMaskCoefficients 6)
      (generatedAxisGlobalFifthInputMaskData 8 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot06ShortPhaseData 8 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-6 Q image. -/
theorem generatedAxisGlobalFifthRoot06Short08_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 6 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 8 i))) =
      qCentral (generatedAxisGlobalFifthRoot06ShortPhaseData 8 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot06ShortLabelData 8 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 6 generatedAxisGlobalFifthQCache06_actual,
    generatedAxisGlobalShortIndexedMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot06Short08_vector_checked i)
    (generatedAxisGlobalFifthRoot06Short08_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
