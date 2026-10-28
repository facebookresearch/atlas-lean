/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW16pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W16+ (Twelfth
    root 16 to Tenth root 28, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW16p_ha0 : oddWZT 64 true fbW16pHX (OctadDense.octChunkTerms fbW16pGC0) = 16896 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW16p_ha1 : oddWZT 64 true fbW16pHX (OctadDense.octChunkTerms fbW16pGC1) = 16606 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW16p_ha2 : oddWZT 64 true fbW16pHX (OctadDense.octChunkTerms fbW16pGC2) = 17368 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW16p_ha3 : oddWZT 64 true fbW16pHX (OctadDense.octChunkTerms fbW16pGC3) = 13130 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW16p_ha : oddWZ 64 true fbW16pHX fbW16pW = 16896 + 16606 + 17368 + 13130 := by
  rw [oddWZ_ofList 64 true fbW16pHX fbW16pW fbW16pGT rfl]
  simp only [fbW16pGT, fbW16pGC, octChunkTerms_append, oddWZT_append, fbW16p_ha0, fbW16p_ha1,
      fbW16p_ha2, fbW16p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
