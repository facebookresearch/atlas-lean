/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T3+
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tv3p_hb0 : oddLZT 64 true tv3pGX (OctadDense.octChunkTerms tv3pHC0) = 16302 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tv3p_hb1 : oddLZT 64 true tv3pGX (OctadDense.octChunkTerms tv3pHC1) = 15166 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tv3p_hb2 : oddLZT 64 true tv3pGX (OctadDense.octChunkTerms tv3pHC2) = 19552 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tv3p_hb3 : oddLZT 64 true tv3pGX (OctadDense.octChunkTerms tv3pHC3) = 13236 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tv3p_hb : oddLZ 64 true tv3pGX tv3pL = 16302 + 15166 + 19552 + 13236 := by
  rw [oddLZ_ofList 64 true tv3pGX tv3pL tv3pHT rfl]
  simp only [tv3pHT, tv3pHC, octChunkTerms_append, oddLZT_append, tv3p_hb0, tv3p_hb1, tv3p_hb2,
      tv3p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tv3p_hc : tdotM 64 (trialityTensorT 64 (!true) tv3pHX) tv3pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
