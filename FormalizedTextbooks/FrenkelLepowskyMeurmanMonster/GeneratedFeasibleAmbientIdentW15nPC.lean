/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W15-
    (Twelfth root 15 to Tenth root 38, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW15n_hb0 : oddLZT 64 false fbW15nGX (OctadDense.octChunkTerms fbW15nHC0) = 62208 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW15n_hb1 : oddLZT 64 false fbW15nGX (OctadDense.octChunkTerms fbW15nHC1) = 64768 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW15n_hb2 : oddLZT 64 false fbW15nGX (OctadDense.octChunkTerms fbW15nHC2) = 65536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW15n_hb3 : oddLZT 64 false fbW15nGX (OctadDense.octChunkTerms fbW15nHC3) = 65536 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW15n_hb : oddLZ 64 false fbW15nGX fbW15nL = 62208 + 64768 + 65536 + 65536 := by
  rw [oddLZ_ofList 64 false fbW15nGX fbW15nL fbW15nHT rfl]
  simp only [fbW15nHT, fbW15nHC, octChunkTerms_append, oddLZT_append, fbW15n_hb0, fbW15n_hb1,
      fbW15n_hb2, fbW15n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW15n_hc : tdotM 64 (trialityTensorT 64 (!false) fbW15nHX) fbW15nGX = 128000 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
