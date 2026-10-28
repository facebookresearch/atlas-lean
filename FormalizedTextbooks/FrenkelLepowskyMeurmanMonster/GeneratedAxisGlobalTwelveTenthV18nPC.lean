/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing parts (odd short terms of the source, tensor) of the Tenth identification T18-
    (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 0. -/
theorem tv18n_hb0 : oddLZT 64 false tv18nGX (OctadDense.octChunkTerms tv18nHC0) = 17532 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 1. -/
theorem tv18n_hb1 : oddLZT 64 false tv18nGX (OctadDense.octChunkTerms tv18nHC1) = 16228 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 2. -/
theorem tv18n_hb2 : oddLZT 64 false tv18nGX (OctadDense.octChunkTerms tv18nHC2) = 17392 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddLZ`, chunk group 3. -/
theorem tv18n_hb3 : oddLZT 64 false tv18nGX (OctadDense.octChunkTerms tv18nHC3) = 13104 := by
  decide +kernel

/-- The odd part `oddLZ` of the pairing (sum of the chunk groups). -/
theorem tv18n_hb : oddLZ 64 false tv18nGX tv18nL = 17532 + 16228 + 17392 + 13104 := by
  rw [oddLZ_ofList 64 false tv18nGX tv18nL tv18nHT rfl]
  simp only [tv18nHT, tv18nHC, octChunkTerms_append, oddLZT_append, tv18n_hb0, tv18n_hb1,
      tv18n_hb2, tv18n_hb3]

set_option maxRecDepth 100000 in
/-- The tensor part of the pairing. -/
theorem tv18n_hc : tdotM 64 (trialityTensorT 64 (!false) tv18nHX) tv18nGX = 128512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
