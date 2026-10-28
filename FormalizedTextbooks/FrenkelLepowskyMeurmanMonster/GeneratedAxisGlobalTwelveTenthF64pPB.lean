/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T64+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tf64p_ha0 : oddWZT 64 true tf64pHX (OctadDense.octChunkTerms tf64pGC0) = 17792 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tf64p_ha : oddWZ 64 true tf64pHX tf64pW = 17792 := by
  rw [oddWZ_ofList 64 true tf64pHX tf64pW tf64pGT rfl]
  simp only [tf64pGT, tf64pGC, tf64p_ha0]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
