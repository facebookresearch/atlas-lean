/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T64+
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tf64p_hb0 : oddLZT 64 true tf64pGX (OctadDense.octChunkTerms tf64pHC0) = 15836 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tf64p_hb1 : oddLZT 64 true tf64pGX (OctadDense.octChunkTerms tf64pHC1) = 14800 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tf64p_hb2 : oddLZT 64 true tf64pGX (OctadDense.octChunkTerms tf64pHC2) = 14600 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tf64p_hb3 : oddLZT 64 true tf64pGX (OctadDense.octChunkTerms tf64pHC3) = 12108 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tf64p_hb : oddLZ 64 true tf64pGX tf64pL = 15836 + 14800 + 14600 + 12108 := by
  rw [oddLZ_ofList 64 true tf64pGX tf64pL tf64pHT rfl]
  simp only [tf64pHT, tf64pHC, octChunkTerms_append, oddLZT_append, tf64p_hb0, tf64p_hb1,
      tf64p_hb2, tf64p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tf64p_hc : tdotM 64 (trialityTensorT 64 (!true) tf64pHX) tf64pGX = 114688 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
