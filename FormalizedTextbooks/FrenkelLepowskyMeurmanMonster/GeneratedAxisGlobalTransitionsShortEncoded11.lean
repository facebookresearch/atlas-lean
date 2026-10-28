/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMaskEncode
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShort11Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache00

/-! Complete first-root packet batch11 from original preferred-Q coordinates and exact bit masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check256 full output masks computed from the original physical preferred-lift formulas.
set_option maxRecDepth 10000 in
/-- Every entire encoded binary image equals the complete original output coordinates. -/
theorem generatedAxisGlobalFifthRoot00Short11_encoded_vector (i : Fin 256) :
    generatedAxisGlobalQMaskVector (generatedAxisGlobalFifthQCacheBinary 0)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalFifthPacketQFinite
        (generatedAxisGlobalFifthRoot00Short11Input i)).base)) =
      generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalShortQFinite
        (generatedAxisGlobalFifthRoot00Short11Label i)).base) := by
  revert i
  decide +kernel

set_option maxHeartbeats 200000000 in
-- Check256 complete original central phases from the actual cochain and original input section.
set_option maxRecDepth 10000 in
/-- Every encoded central bit equals the complete original preferred-lift phase. -/
theorem generatedAxisGlobalFifthRoot00Short11_encoded_central (i : Fin 256) :
    (if (generatedAxisGlobalQMaskCentral (generatedAxisGlobalFifthMaskRows 0)
      (generatedAxisGlobalFifthMaskCoefficients 0)
      (generatedAxisGlobalMaskEncode (toAdd (generatedAxisGlobalFifthPacketQFinite
        (generatedAxisGlobalFifthRoot00Short11Input i)).base))).testBit 0 then
        (1 : ZMod 2) else 0) = generatedAxisGlobalFifthRoot00Short11Phase i := by
  revert i
  decide +kernel

/-- The exact original preferred-Q image follows from two full encoded certificates. -/
theorem generatedAxisGlobalFifthRoot00Short11_encoded_QImage (i : Fin 256) :
    generatedAxisGlobalFifthQFast 0
      (generatedAxisGlobalFifthPacketQFinite (generatedAxisGlobalFifthRoot00Short11Input i)) =
      qCentral (generatedAxisGlobalFifthRoot00Short11Phase i) *
        generatedAxisGlobalShortQFinite (generatedAxisGlobalFifthRoot00Short11Label i) :=
  generatedAxisGlobalFifthMaskCheck_actual 0 generatedAxisGlobalFifthQCache00_actual _ _ _
    (generatedAxisGlobalFifthPacketQFinite_positive _)
    (generatedAxisGlobalShortQFinite_positive _)
    (generatedAxisGlobalFifthRoot00Short11_encoded_vector i)
    (generatedAxisGlobalFifthRoot00Short11_encoded_central i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
