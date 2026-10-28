/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW29pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the identification gtwelfth:W29+ (Twelfth root 29 to Tenth root 48,
    e = 1) (H side)

Group by group against the literal groups of the source flat short list. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of group 0 (H). -/
theorem fbW29pHT_g0 :
    shortCheckF fbW29pHD fbt12G0
      (OctadDense.octChunkTerms fbW29pHC0) = true :=
  shortCheckPk_sound _ 10 12 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 1 (H). -/
theorem fbW29pHT_g1 :
    shortCheckF fbW29pHD fbt12G1
      (OctadDense.octChunkTerms fbW29pHC1) = true :=
  shortCheckPk_sound _ 10 11 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 2 (H). -/
theorem fbW29pHT_g2 :
    shortCheckF fbW29pHD fbt12G2
      (OctadDense.octChunkTerms fbW29pHC2) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 3 (H). -/
theorem fbW29pHT_g3 :
    shortCheckF fbW29pHD fbt12G3
      (OctadDense.octChunkTerms fbW29pHC3) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

/-- The short block of the H image is the checked transport of the source short block. -/
theorem fbW29pHT_check : shortCheckF fbW29pHD (twelfthSrcVecS 64).sh.flat fbW29pHT = true := by
  have hS : (twelfthSrcVecS 64).sh.flat =
      fbt12G0 ++ (fbt12G1 ++ (fbt12G2 ++ (fbt12G3))) := by
    rw [fbt12V_flat]
    simp only [List.append_assoc]
  simp only [fbW29pHT, fbW29pHC, octChunkTerms_append, List.append_assoc]
  rw [hS]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW29pHT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW29pHT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW29pHT_g2
      fbW29pHT_g3)))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
