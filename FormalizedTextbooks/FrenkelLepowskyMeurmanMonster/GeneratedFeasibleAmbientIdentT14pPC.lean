/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtenth:T14+
    (Tenth root 14 to Twelfth root 7, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbT14p_hb0 : oddLZT 64 true fbT14pGX (OctadDense.octChunkTerms fbT14pHC0) = 17164 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbT14p_hb1 : oddLZT 64 true fbT14pGX (OctadDense.octChunkTerms fbT14pHC1) = 15740 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbT14p_hb2 : oddLZT 64 true fbT14pGX (OctadDense.octChunkTerms fbT14pHC2) = 17720 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbT14p_hb3 : oddLZT 64 true fbT14pGX (OctadDense.octChunkTerms fbT14pHC3) = 13120 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbT14p_hb : oddLZ 64 true fbT14pGX fbT14pL = 17164 + 15740 + 17720 + 13120 := by
  rw [oddLZ_ofList 64 true fbT14pGX fbT14pL fbT14pHT rfl]
  simp only [fbT14pHT, fbT14pHC, octChunkTerms_append, oddLZT_append, fbT14p_hb0, fbT14p_hb1,
      fbT14p_hb2, fbT14p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbT14p_hc : tdotM 64 (trialityTensorT 64 (!true) fbT14pHX) fbT14pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
