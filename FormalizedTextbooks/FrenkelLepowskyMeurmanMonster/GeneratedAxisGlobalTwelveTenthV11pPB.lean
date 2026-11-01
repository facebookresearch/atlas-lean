/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T11+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tv11p_ha0 : oddWZT 64 true tv11pHX (OctadDense.octChunkTerms tv11pGC0) = 16142 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem tv11p_ha1 : oddWZT 64 true tv11pHX (OctadDense.octChunkTerms tv11pGC1) = 15612 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem tv11p_ha2 : oddWZT 64 true tv11pHX (OctadDense.octChunkTerms tv11pGC2) = 18122 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem tv11p_ha3 : oddWZT 64 true tv11pHX (OctadDense.octChunkTerms tv11pGC3) = 14380 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tv11p_ha : oddWZ 64 true tv11pHX tv11pW = 16142 + 15612 + 18122 + 14380 := by
  rw [oddWZ_ofList 64 true tv11pHX tv11pW tv11pGT rfl]
  simp only [tv11pGT, tv11pGC, octChunkTerms_append, oddWZT_append, tv11p_ha0, tv11p_ha1,
      tv11p_ha2, tv11p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
