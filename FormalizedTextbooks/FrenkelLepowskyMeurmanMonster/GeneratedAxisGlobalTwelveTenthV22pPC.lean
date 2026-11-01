/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV22pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T22+
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tv22p_hb0 : oddLZT 64 true tv22pGX (OctadDense.octChunkTerms tv22pHC0) = 16462 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tv22p_hb1 : oddLZT 64 true tv22pGX (OctadDense.octChunkTerms tv22pHC1) = 15586 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tv22p_hb2 : oddLZT 64 true tv22pGX (OctadDense.octChunkTerms tv22pHC2) = 19124 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tv22p_hb3 : oddLZT 64 true tv22pGX (OctadDense.octChunkTerms tv22pHC3) = 13084 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tv22p_hb : oddLZ 64 true tv22pGX tv22pL = 16462 + 15586 + 19124 + 13084 := by
  rw [oddLZ_ofList 64 true tv22pGX tv22pL tv22pHT rfl]
  simp only [tv22pHT, tv22pHC, octChunkTerms_append, oddLZT_append, tv22p_hb0, tv22p_hb1,
      tv22p_hb2, tv22p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tv22p_hc : tdotM 64 (trialityTensorT 64 (!true) tv22pHX) tv22pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
