/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW15nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Pairing part (odd short terms of the target) of the identification gtwelfth:W15- (Twelfth
    root 15 to Tenth root 38, e = -1) -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 0. -/
theorem fbW15n_ha0 : oddWZT 64 false fbW15nHX (OctadDense.octChunkTerms fbW15nGC0) = 16878 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 1. -/
theorem fbW15n_ha1 : oddWZT 64 false fbW15nHX (OctadDense.octChunkTerms fbW15nGC1) = 15826 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 2. -/
theorem fbW15n_ha2 : oddWZT 64 false fbW15nHX (OctadDense.octChunkTerms fbW15nGC2) = 17548 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Odd part `oddWZ`, chunk group 3. -/
theorem fbW15n_ha3 : oddWZT 64 false fbW15nHX (OctadDense.octChunkTerms fbW15nGC3) = 13748 := by
  decide +kernel

/-- The odd part `oddWZ` of the pairing (sum of the chunk groups). -/
theorem fbW15n_ha : oddWZ 64 false fbW15nHX fbW15nW = 16878 + 15826 + 17548 + 13748 := by
  rw [oddWZ_ofList 64 false fbW15nHX fbW15nW fbW15nGT rfl]
  simp only [fbW15nGT, fbW15nGC, octChunkTerms_append, oddWZT_append, fbW15n_ha0, fbW15n_ha1,
      fbW15n_ha2, fbW15n_ha3]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
