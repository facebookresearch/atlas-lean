/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW17pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W17+ (Twelfth
    root 17 to Tenth root 44, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW17p_ha0 : oddWZT 64 true fbW17pHX (OctadDense.octChunkTerms fbW17pGC0) = 17536 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW17p_ha1 : oddWZT 64 true fbW17pHX (OctadDense.octChunkTerms fbW17pGC1) = 15966 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW17p_ha2 : oddWZT 64 true fbW17pHX (OctadDense.octChunkTerms fbW17pGC2) = 17368 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW17p_ha3 : oddWZT 64 true fbW17pHX (OctadDense.octChunkTerms fbW17pGC3) = 13130 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW17p_ha : oddWZ 64 true fbW17pHX fbW17pW = 17536 + 15966 + 17368 + 13130 := by
  rw [oddWZ_ofList 64 true fbW17pHX fbW17pW fbW17pGT rfl]
  simp only [fbW17pGT, fbW17pGC, octChunkTerms_append, oddWZT_append, fbW17p_ha0, fbW17p_ha1,
      fbW17p_ha2, fbW17p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
