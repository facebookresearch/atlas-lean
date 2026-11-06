/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR01Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache01

/-! Complete original second-root preferred-Q transport for packet batch1. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot01Short01_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 1)
      (generatedAxisGlobalFifthInputMaskData 1 i) =
      generatedAxisGlobalShortMask (generatedAxisGlobalFifthRoot01ShortLabelData 1 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot01Short01_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 1)
      (generatedAxisGlobalFifthMaskCoefficients 1)
      (generatedAxisGlobalFifthInputMaskData 1 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot01ShortPhaseData 1 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original second-root Q image. -/
theorem generatedAxisGlobalFifthRoot01Short01_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 1 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 1 i))) =
      qCentral (generatedAxisGlobalFifthRoot01ShortPhaseData 1 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot01ShortLabelData 1 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 1 generatedAxisGlobalFifthQCache01_actual,
    generatedAxisGlobalShortMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot01Short01_vector_checked i)
    (generatedAxisGlobalFifthRoot01Short01_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
