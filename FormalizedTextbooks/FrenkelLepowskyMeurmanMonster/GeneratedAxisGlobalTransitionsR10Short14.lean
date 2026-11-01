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
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR10Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache10

/-! Complete original root-10 preferred-Q transport for packet batch14. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot10Short14_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 10)
      (generatedAxisGlobalFifthInputMaskData 14 i) =
      generatedAxisGlobalShortIndexedMask (generatedAxisGlobalFifthRoot10ShortLabelData 14 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot10Short14_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 10)
      (generatedAxisGlobalFifthMaskCoefficients 10)
      (generatedAxisGlobalFifthInputMaskData 14 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot10ShortPhaseData 14 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-10 Q image. -/
theorem generatedAxisGlobalFifthRoot10Short14_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 10 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 14 i))) =
      qCentral (generatedAxisGlobalFifthRoot10ShortPhaseData 14 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot10ShortLabelData 14 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 10 generatedAxisGlobalFifthQCache10_actual,
    generatedAxisGlobalShortIndexedMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot10Short14_vector_checked i)
    (generatedAxisGlobalFifthRoot10Short14_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
