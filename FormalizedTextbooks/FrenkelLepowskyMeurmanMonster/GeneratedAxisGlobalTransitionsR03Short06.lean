/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortSparseMask
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsR03Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthInputCompact
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache03

/-! Complete original root-3 preferred-Q transport for packet batch6. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks against the original physical preferred-Q formulas.
set_option maxRecDepth 10000 in
/-- Every output word is the complete original binary image of this packet entry. -/
theorem generatedAxisGlobalFifthRoot03Short06_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 3)
      (generatedAxisGlobalFifthInputMaskData 6 i) =
      generatedAxisGlobalShortSparseMask (generatedAxisGlobalFifthRoot03ShortLabelData 6 i) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 original central signs against the actual triangular cochain and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the complete original preferred-lift sign. -/
theorem generatedAxisGlobalFifthRoot03Short06_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 3)
      (generatedAxisGlobalFifthMaskCoefficients 3)
      (generatedAxisGlobalFifthInputMaskData 6 i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot03ShortPhaseData 6 i := by
  revert i
  decide +kernel

/-- Two full bit certificates give the complete genuine original root-3 Q image. -/
theorem generatedAxisGlobalFifthRoot03Short06_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 3 (generatedAxisGlobalFifthPacketQFinite
      (generatedAxisGlobalFifthPacketFromNumber
        (generatedAxisGlobalFifthPacketBatchNumber 6 i))) =
      qCentral (generatedAxisGlobalFifthRoot03ShortPhaseData 6 i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot03ShortLabelData 6 i) := by
  rw [generatedAxisGlobalFifthInputCompact_data_Q_actual,
    generatedAxisGlobalFifthQFast_mask 3 generatedAxisGlobalFifthQCache03_actual,
    generatedAxisGlobalShortSparseMask_Q_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot03Short06_vector_checked i)
    (generatedAxisGlobalFifthRoot03Short06_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
