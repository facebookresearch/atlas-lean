/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W10- (Twelfth
    root 10 to Tenth root 51, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW10n_ha0 : oddWZT 64 false fbW10nHX (OctadDense.octChunkTerms fbW10nGC0) = 16366 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW10n_ha1 : oddWZT 64 false fbW10nHX (OctadDense.octChunkTerms fbW10nGC1) = 15314 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW10n_ha2 : oddWZT 64 false fbW10nHX (OctadDense.octChunkTerms fbW10nGC2) = 19076 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW10n_ha3 : oddWZT 64 false fbW10nHX (OctadDense.octChunkTerms fbW10nGC3) = 11196 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW10n_ha : oddWZ 64 false fbW10nHX fbW10nW = 16366 + 15314 + 19076 + 11196 := by
  rw [oddWZ_ofList 64 false fbW10nHX fbW10nW fbW10nGT rfl]
  simp only [fbW10nGT, fbW10nGC, octChunkTerms_append, oddWZT_append, fbW10n_ha0, fbW10n_ha1,
      fbW10n_ha2, fbW10n_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
