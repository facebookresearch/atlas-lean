/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW2nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W2- (Twelfth
    root 2 to Tenth root 8, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW2n_ha0 : oddWZT 64 false fbW2nHX (OctadDense.octChunkTerms fbW2nGC0) = 17628 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW2n_ha1 : oddWZT 64 false fbW2nHX (OctadDense.octChunkTerms fbW2nGC1) = 15876 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW2n_ha2 : oddWZT 64 false fbW2nHX (OctadDense.octChunkTerms fbW2nGC2) = 17384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW2n_ha3 : oddWZT 64 false fbW2nHX (OctadDense.octChunkTerms fbW2nGC3) = 13112 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW2n_ha : oddWZ 64 false fbW2nHX fbW2nW = 17628 + 15876 + 17384 + 13112 := by
  rw [oddWZ_ofList 64 false fbW2nHX fbW2nW fbW2nGT rfl]
  simp only [fbW2nGT, fbW2nGC, octChunkTerms_append, oddWZT_append, fbW2n_ha0, fbW2n_ha1,
      fbW2n_ha2, fbW2n_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
