/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W2-
    (Twelfth root 2 to Tenth root 8, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW2n_hb0 : oddLZT 64 false fbW2nGX (OctadDense.octChunkTerms fbW2nHC0) = 67456 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW2n_hb1 : oddLZT 64 false fbW2nGX (OctadDense.octChunkTerms fbW2nHC1) = 59520 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW2n_hb2 : oddLZT 64 false fbW2nGX (OctadDense.octChunkTerms fbW2nHC2) = 65536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW2n_hb3 : oddLZT 64 false fbW2nGX (OctadDense.octChunkTerms fbW2nHC3) = 65536 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW2n_hb : oddLZ 64 false fbW2nGX fbW2nL = 67456 + 59520 + 65536 + 65536 := by
  rw [oddLZ_ofList 64 false fbW2nGX fbW2nL fbW2nHT rfl]
  simp only [fbW2nHT, fbW2nHC, octChunkTerms_append, oddLZT_append, fbW2n_hb0, fbW2n_hb1,
      fbW2n_hb2, fbW2n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW2n_hc : tdotM 64 (trialityTensorT 64 (!false) fbW2nHX) fbW2nGX = 128000 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
