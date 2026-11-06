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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR12Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache12

/-! Complete original root-12 preferred-Q transport for packet batch16. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot12Short16_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 12)
      (generatedAxisGlobalFifthInputMaskData 16 i) =
      generatedAxisGlobalShortIndexedMask (generatedAxisGlobalFifthRoot12ShortLabelData 16 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot12Short16_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 12)
      (generatedAxisGlobalFifthMaskCoefficients 12)
      (generatedAxisGlobalFifthInputMaskData 16 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot12ShortPhaseData 16 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-12 Q image. -/
theorem generatedAxisGlobalFifthRoot12Short16_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 12 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 16 i))) =
      qCentral (generatedAxisGlobalFifthRoot12ShortPhaseData 16 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot12ShortLabelData 16 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 12 generatedAxisGlobalFifthQCache12_actual,
    generatedAxisGlobalShortIndexedMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot12Short16_vector_checked i)
    (generatedAxisGlobalFifthRoot12Short16_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
