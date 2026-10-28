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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR13Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache13

/-! Complete original root-13 preferred-Q transport for packet batch2. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot13Short02_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 13)
      (generatedAxisGlobalFifthInputMaskData 2 i) =
      generatedAxisGlobalShortIndexedMask (generatedAxisGlobalFifthRoot13ShortLabelData 2 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot13Short02_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 13)
      (generatedAxisGlobalFifthMaskCoefficients 13)
      (generatedAxisGlobalFifthInputMaskData 2 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot13ShortPhaseData 2 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-13 Q image. -/
theorem generatedAxisGlobalFifthRoot13Short02_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 13 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 2 i))) =
      qCentral (generatedAxisGlobalFifthRoot13ShortPhaseData 2 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot13ShortLabelData 2 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 13 generatedAxisGlobalFifthQCache13_actual,
    generatedAxisGlobalShortIndexedMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot13Short02_vector_checked i)
    (generatedAxisGlobalFifthRoot13Short02_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
