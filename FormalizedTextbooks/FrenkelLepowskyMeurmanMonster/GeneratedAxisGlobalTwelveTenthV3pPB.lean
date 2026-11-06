/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T3+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tv3p_ha0 : oddWZT 64 true tv3pHX (OctadDense.octChunkTerms tv3pGC0) = 16302 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem tv3p_ha1 : oddWZT 64 true tv3pHX (OctadDense.octChunkTerms tv3pGC1) = 15166 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem tv3p_ha2 : oddWZT 64 true tv3pHX (OctadDense.octChunkTerms tv3pGC2) = 19552 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem tv3p_ha3 : oddWZT 64 true tv3pHX (OctadDense.octChunkTerms tv3pGC3) = 13236 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tv3p_ha : oddWZ 64 true tv3pHX tv3pW = 16302 + 15166 + 19552 + 13236 := by
  rw [oddWZ_ofList 64 true tv3pHX tv3pW tv3pGT rfl]
  simp only [tv3pGT, tv3pGC, octChunkTerms_append, oddWZT_append, tv3p_ha0, tv3p_ha1, tv3p_ha2,
      tv3p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
