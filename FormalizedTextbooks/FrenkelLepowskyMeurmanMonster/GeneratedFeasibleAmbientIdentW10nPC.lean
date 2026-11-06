/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the identification gtwelfth:W10-
    (Twelfth root 10 to Tenth root 51, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem fbW10n_hb0 : oddLZT 64 false fbW10nGX (OctadDense.octChunkTerms fbW10nHC0) = 65792 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem fbW10n_hb1 : oddLZT 64 false fbW10nGX (OctadDense.octChunkTerms fbW10nHC1) = 52992 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem fbW10n_hb2 : oddLZT 64 false fbW10nGX (OctadDense.octChunkTerms fbW10nHC2) = 65536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem fbW10n_hb3 : oddLZT 64 false fbW10nGX (OctadDense.octChunkTerms fbW10nHC3) = 65536 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem fbW10n_hb : oddLZ 64 false fbW10nGX fbW10nL = 65792 + 52992 + 65536 + 65536 := by
  rw [oddLZ_ofList 64 false fbW10nGX fbW10nL fbW10nHT rfl]
  simp only [fbW10nHT, fbW10nHC, octChunkTerms_append, oddLZT_append, fbW10n_hb0, fbW10n_hb1,
      fbW10n_hb2, fbW10n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem fbW10n_hc : tdotM 64 (trialityTensorT 64 (!false) fbW10nHX) fbW10nGX = 132096 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
