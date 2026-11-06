/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtenth:T14+ (Tenth root
    14 to Twelfth root 7, e = 1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbT14p_ha0 : oddWZT 64 true fbT14pHX (OctadDense.octChunkTerms fbT14pGC0) = 66944 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbT14p_ha1 : oddWZT 64 true fbT14pHX (OctadDense.octChunkTerms fbT14pGC1) = 54912 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbT14p_ha2 : oddWZT 64 true fbT14pHX (OctadDense.octChunkTerms fbT14pGC2) = 64512 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbT14p_ha3 : oddWZT 64 true fbT14pHX (OctadDense.octChunkTerms fbT14pGC3) = 70656 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbT14p_ha : oddWZ 64 true fbT14pHX fbT14pW = 66944 + 54912 + 64512 + 70656 := by
  rw [oddWZ_ofList 64 true fbT14pHX fbT14pW fbT14pGT rfl]
  simp only [fbT14pGT, fbT14pGC, octChunkTerms_append, oddWZT_append, fbT14p_ha0, fbT14p_ha1,
      fbT14p_ha2, fbT14p_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
