/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentT14pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelfthSrcG
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the identification gtenth:T14+ (Tenth root 14 to Twelfth root 7, e
    = 1) (G side)

Group by group against the literal groups of the source flat short list. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of group 0 (G). -/
theorem fbT14pGT_g0 :
    shortCheckF fbT14pGD fbt12G0
      (OctadDense.octChunkTerms fbT14pGC0) = true :=
  shortCheckPk_sound _ 10 12 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 1 (G). -/
theorem fbT14pGT_g1 :
    shortCheckF fbT14pGD fbt12G1
      (OctadDense.octChunkTerms fbT14pGC1) = true :=
  shortCheckPk_sound _ 10 11 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 2 (G). -/
theorem fbT14pGT_g2 :
    shortCheckF fbT14pGD fbt12G2
      (OctadDense.octChunkTerms fbT14pGC2) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 3 (G). -/
theorem fbT14pGT_g3 :
    shortCheckF fbT14pGD fbt12G3
      (OctadDense.octChunkTerms fbT14pGC3) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

/-- The short block of the G image is the checked transport of the source short block. -/
theorem fbT14pGT_check : shortCheckF fbT14pGD (twelfthSrcVecS 64).sh.flat fbT14pGT = true := by
  have hS : (twelfthSrcVecS 64).sh.flat =
      fbt12G0 ++ (fbt12G1 ++ (fbt12G2 ++ (fbt12G3))) := by
    rw [fbt12V_flat]
    simp only [List.append_assoc]
  simp only [fbT14pGT, fbT14pGC, octChunkTerms_append, List.append_assoc]
  rw [hS]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbT14pGT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbT14pGT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbT14pGT_g2
      fbT14pGT_g3)))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
