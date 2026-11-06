/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV18nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the Tenth identification T18- (gtenth) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem tv18n_ha0 : oddWZT 64 false tv18nHX (OctadDense.octChunkTerms tv18nGC0) = 17532 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem tv18n_ha1 : oddWZT 64 false tv18nHX (OctadDense.octChunkTerms tv18nGC1) = 16228 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem tv18n_ha2 : oddWZT 64 false tv18nHX (OctadDense.octChunkTerms tv18nGC2) = 17392 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem tv18n_ha3 : oddWZT 64 false tv18nHX (OctadDense.octChunkTerms tv18nGC3) = 13104 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem tv18n_ha : oddWZ 64 false tv18nHX tv18nW = 17532 + 16228 + 17392 + 13104 := by
  rw [oddWZ_ofList 64 false tv18nHX tv18nW tv18nGT rfl]
  simp only [tv18nGT, tv18nGC, octChunkTerms_append, oddWZT_append, tv18n_ha0, tv18n_ha1,
      tv18n_ha2, tv18n_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
