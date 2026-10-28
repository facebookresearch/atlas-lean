/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W29+
    (Twelfth root 29 to Tenth root 48, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW29p_hb0 : oddLZT 64 true fbW29pGX (OctadDense.octChunkTerms fbW29pHC0) = 56832 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW29p_hb1 : oddLZT 64 true fbW29pGX (OctadDense.octChunkTerms fbW29pHC1) = 51712 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW29p_hb2 : oddLZT 64 true fbW29pGX (OctadDense.octChunkTerms fbW29pHC2) = 77824 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW29p_hb3 : oddLZT 64 true fbW29pGX (OctadDense.octChunkTerms fbW29pHC3) = 70656 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW29p_hb : oddLZ 64 true fbW29pGX fbW29pL = 56832 + 51712 + 77824 + 70656 := by
  rw [oddLZ_ofList 64 true fbW29pGX fbW29pL fbW29pHT rfl]
  simp only [fbW29pHT, fbW29pHC, octChunkTerms_append, oddLZT_append, fbW29p_hb0, fbW29p_hb1,
      fbW29p_hb2, fbW29p_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW29p_hc : tdotM 64 (trialityTensorT 64 (!true) fbW29pHX) fbW29pGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
