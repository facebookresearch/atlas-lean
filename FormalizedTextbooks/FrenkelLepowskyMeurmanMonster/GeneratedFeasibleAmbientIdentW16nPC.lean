/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W16-
    (Twelfth root 16 to Tenth root 28, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW16n_hb0 : oddLZT 64 false fbW16nGX (OctadDense.octChunkTerms fbW16nHC0) = 67584 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW16n_hb1 : oddLZT 64 false fbW16nGX (OctadDense.octChunkTerms fbW16nHC1) = 59392 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW16n_hb2 : oddLZT 64 false fbW16nGX (OctadDense.octChunkTerms fbW16nHC2) = 65536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW16n_hb3 : oddLZT 64 false fbW16nGX (OctadDense.octChunkTerms fbW16nHC3) = 65536 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW16n_hb : oddLZ 64 false fbW16nGX fbW16nL = 67584 + 59392 + 65536 + 65536 := by
  rw [oddLZ_ofList 64 false fbW16nGX fbW16nL fbW16nHT rfl]
  simp only [fbW16nHT, fbW16nHC, octChunkTerms_append, oddLZT_append, fbW16n_hb0, fbW16n_hb1,
      fbW16n_hb2, fbW16n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW16n_hc : tdotM 64 (trialityTensorT 64 (!false) fbW16nHX) fbW16nGX = 128000 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
