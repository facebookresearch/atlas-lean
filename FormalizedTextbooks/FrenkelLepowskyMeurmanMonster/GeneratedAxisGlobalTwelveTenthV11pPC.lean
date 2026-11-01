/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV11pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T11+
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tv11p_hb0 : oddLZT 64 true tv11pGX (OctadDense.octChunkTerms tv11pHC0) = 16142 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tv11p_hb1 : oddLZT 64 true tv11pGX (OctadDense.octChunkTerms tv11pHC1) = 15612 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tv11p_hb2 : oddLZT 64 true tv11pGX (OctadDense.octChunkTerms tv11pHC2) = 18122 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tv11p_hb3 : oddLZT 64 true tv11pGX (OctadDense.octChunkTerms tv11pHC3) = 14380 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tv11p_hb : oddLZ 64 true tv11pGX tv11pL = 16142 + 15612 + 18122 + 14380 := by
  rw [oddLZ_ofList 64 true tv11pGX tv11pL tv11pHT rfl]
  simp only [tv11pHT, tv11pHC, octChunkTerms_append, oddLZT_append, tv11p_hb0, tv11p_hb1,
      tv11p_hb2, tv11p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tv11p_hc : tdotM 64 (trialityTensorT 64 (!true) tv11pHX) tv11pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
