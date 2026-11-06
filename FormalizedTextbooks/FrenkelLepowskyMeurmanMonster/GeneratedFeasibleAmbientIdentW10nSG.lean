/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIdentW10nData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the identification gtwelfth:W10- (Twelfth root 10 to Tenth root 51,
    e = -1) (G side)

Group by group against the literal groups of the source flat short list. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of group 0 (G). -/
theorem fbW10nGT_g0 :
    shortCheckF fbW10nGD (t10SG0 ++ t10SG1 ++ t10SG2)
      (OctadDense.octChunkTerms fbW10nGC0) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 1 (G). -/
theorem fbW10nGT_g1 :
    shortCheckF fbW10nGD (t10SG3 ++ t10SG4 ++ t10SG5)
      (OctadDense.octChunkTerms fbW10nGC1) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 2 (G). -/
theorem fbW10nGT_g2 :
    shortCheckF fbW10nGD (t10SG6 ++ t10SG7 ++ t10SG8)
      (OctadDense.octChunkTerms fbW10nGC2) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 3 (G). -/
theorem fbW10nGT_g3 :
    shortCheckF fbW10nGD (t10SG9 ++ t10SG10 ++ t10SG11)
      (OctadDense.octChunkTerms fbW10nGC3) = true :=
  shortCheckPk_sound _ 10 10 _ _ (by decide +kernel)

/-- The short block of the G image is the checked transport of the source short block. -/
theorem fbW10nGT_check : shortCheckF fbW10nGD t10V.sh.flat fbW10nGT = true := by
  have hS : t10V.sh.flat =
      (t10SG0 ++ t10SG1 ++ t10SG2) ++ ((t10SG3 ++ t10SG4 ++ t10SG5) ++ ((t10SG6 ++ t10SG7 ++
          t10SG8) ++ ((t10SG9 ++ t10SG10 ++ t10SG11)))) := by
    rw [t10V_flat]
    simp only [List.append_assoc]
  simp only [fbW10nGT, fbW10nGC, octChunkTerms_append, List.append_assoc]
  rw [hS]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW10nGT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW10nGT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) fbW10nGT_g2
      fbW10nGT_g3)))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
