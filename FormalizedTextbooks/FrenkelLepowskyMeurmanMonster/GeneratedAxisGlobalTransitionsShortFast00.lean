/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMask00
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMask00

/-! First genuine root packet certified by complete output masks and actual central phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 entire24-bit output words, without expanding the original Q coordinate products.
set_option maxRecDepth 10000 in
/-- Every complete output mask is the exact original binary image. -/
theorem generatedAxisGlobalFifthRoot00Short00_vector_checked (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 0)
        (generatedAxisGlobalFifthRoot00Short00InputMask i) =
      generatedAxisGlobalFifthRoot00Short00OutputMask i := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 actual central signs from the proved triangular cocycle and linear correction.
set_option maxRecDepth 10000 in
/-- Every central bit is the precise original preferred-lift phase. -/
theorem generatedAxisGlobalFifthRoot00Short00_central_checked (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 0)
      (generatedAxisGlobalFifthMaskCoefficients 0)
      (generatedAxisGlobalFifthRoot00Short00InputMask i)).testBit 0 then (1 : ZMod 2) else 0) =
      generatedAxisGlobalFifthRoot00Short00Phase i := by
  revert i
  decide +kernel

/-- The complete original Q image follows from two exact bit certificates and source bindings. -/
theorem generatedAxisGlobalFifthRoot00Short00_fast_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 0
      (generatedAxisGlobalFifthPacketQFinite (generatedAxisGlobalFifthRoot00Short00Input i)) =
      qCentral (generatedAxisGlobalFifthRoot00Short00Phase i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot00Short00Label i) := by
  rw [generatedAxisGlobalFifthRoot00Short00InputMask_actual,
    generatedAxisGlobalFifthRoot00Short00OutputMask_actual, generatedAxisGlobalFifthQFast_mask00]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _
    (generatedAxisGlobalFifthRoot00Short00_vector_checked i)
    (generatedAxisGlobalFifthRoot00Short00_central_checked i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
