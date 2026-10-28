/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW18pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W18+ (Twelfth
    root 18 to Tenth root 36, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW18p_ha0 : oddWZT 64 true fbW18pHX (OctadDense.octChunkTerms fbW18pGC0) = 17116 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW18p_ha1 : oddWZT 64 true fbW18pHX (OctadDense.octChunkTerms fbW18pGC1) = 15808 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW18p_ha2 : oddWZT 64 true fbW18pHX (OctadDense.octChunkTerms fbW18pGC2) = 16604 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW18p_ha3 : oddWZT 64 true fbW18pHX (OctadDense.octChunkTerms fbW18pGC3) = 13704 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW18p_ha : oddWZ 64 true fbW18pHX fbW18pW = 17116 + 15808 + 16604 + 13704 := by
  rw [oddWZ_ofList 64 true fbW18pHX fbW18pW fbW18pGT rfl]
  simp only [fbW18pGT, fbW18pGC, octChunkTerms_append, oddWZT_append, fbW18p_ha0, fbW18p_ha1,
      fbW18p_ha2, fbW18p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
