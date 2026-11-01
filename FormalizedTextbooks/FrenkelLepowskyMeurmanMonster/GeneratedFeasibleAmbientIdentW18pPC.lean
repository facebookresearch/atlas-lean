/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W18+
    (Twelfth root 18 to Tenth root 36, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW18p_hb0 : oddLZT 64 true fbW18pGX (OctadDense.octChunkTerms fbW18pHC0) = 64512 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW18p_hb1 : oddLZT 64 true fbW18pGX (OctadDense.octChunkTerms fbW18pHC1) = 56320 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW18p_hb2 : oddLZT 64 true fbW18pGX (OctadDense.octChunkTerms fbW18pHC2) = 64768 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW18p_hb3 : oddLZT 64 true fbW18pGX (OctadDense.octChunkTerms fbW18pHC3) = 69376 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW18p_hb : oddLZ 64 true fbW18pGX fbW18pL = 64512 + 56320 + 64768 + 69376 := by
  rw [oddLZ_ofList 64 true fbW18pGX fbW18pL fbW18pHT rfl]
  simp only [fbW18pHT, fbW18pHC, octChunkTerms_append, oddLZT_append, fbW18p_hb0, fbW18p_hb1,
      fbW18p_hb2, fbW18p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW18p_hc : tdotM 64 (trialityTensorT 64 (!true) fbW18pHX) fbW18pGX = 129536 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
