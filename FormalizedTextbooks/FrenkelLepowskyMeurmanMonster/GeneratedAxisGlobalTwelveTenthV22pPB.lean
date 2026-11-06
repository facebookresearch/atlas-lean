/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T22+ (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tv22p_ha0 : oddWZT 64 true tv22pHX (OctadDense.octChunkTerms tv22pGC0) = 16462 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem tv22p_ha1 : oddWZT 64 true tv22pHX (OctadDense.octChunkTerms tv22pGC1) = 15586 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem tv22p_ha2 : oddWZT 64 true tv22pHX (OctadDense.octChunkTerms tv22pGC2) = 19124 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem tv22p_ha3 : oddWZT 64 true tv22pHX (OctadDense.octChunkTerms tv22pGC3) = 13084 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tv22p_ha : oddWZ 64 true tv22pHX tv22pW = 16462 + 15586 + 19124 + 13084 := by
  rw [oddWZ_ofList 64 true tv22pHX tv22pW tv22pGT rfl]
  simp only [tv22pGT, tv22pGC, octChunkTerms_append, oddWZT_append, tv22p_ha0, tv22p_ha1,
      tv22p_ha2, tv22p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
