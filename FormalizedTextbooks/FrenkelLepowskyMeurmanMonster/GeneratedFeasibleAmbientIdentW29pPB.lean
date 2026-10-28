/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W29+ (Twelfth
    root 29 to Tenth root 48, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW29p_ha0 : oddWZT 64 true fbW29pHX (OctadDense.octChunkTerms fbW29pGC0) = 16604 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW29p_ha1 : oddWZT 64 true fbW29pHX (OctadDense.octChunkTerms fbW29pGC1) = 16640 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW29p_ha2 : oddWZT 64 true fbW29pHX (OctadDense.octChunkTerms fbW29pGC2) = 17384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW29p_ha3 : oddWZT 64 true fbW29pHX (OctadDense.octChunkTerms fbW29pGC3) = 13116 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW29p_ha : oddWZ 64 true fbW29pHX fbW29pW = 16604 + 16640 + 17384 + 13116 := by
  rw [oddWZ_ofList 64 true fbW29pHX fbW29pW fbW29pGT rfl]
  simp only [fbW29pGT, fbW29pGC, octChunkTerms_append, oddWZT_append, fbW29p_ha0, fbW29p_ha1,
      fbW29p_ha2, fbW29p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
