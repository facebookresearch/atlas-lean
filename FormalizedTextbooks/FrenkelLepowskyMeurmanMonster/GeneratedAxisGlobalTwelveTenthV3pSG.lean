/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV3pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the Tenth identification T3+ (G side)

Group by group (groups of `12288` terms of the scaled Tenth source short block). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of group 0 (G). -/
theorem tv3pGT_g0 :
    shortCheckF tv3pGD (t10SG0 ++ t10SG1 ++ t10SG2)
      (OctadDense.octChunkTerms tv3pGC0) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 1 (G). -/
theorem tv3pGT_g1 :
    shortCheckF tv3pGD (t10SG3 ++ t10SG4 ++ t10SG5)
      (OctadDense.octChunkTerms tv3pGC1) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 2 (G). -/
theorem tv3pGT_g2 :
    shortCheckF tv3pGD (t10SG6 ++ t10SG7 ++ t10SG8)
      (OctadDense.octChunkTerms tv3pGC2) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 3 (G). -/
theorem tv3pGT_g3 :
    shortCheckF tv3pGD (t10SG9 ++ t10SG10 ++ t10SG11)
      (OctadDense.octChunkTerms tv3pGC3) = true :=
  shortCheckPk_sound _ 10 10 _ _ (by decide +kernel)

/-- The short block of the G image is the checked transport of the scaled Tenth source short
block. -/
theorem tv3pGT_check : shortCheckF tv3pGD t10V.sh.flat tv3pGT = true := by
  have hS : t10V.sh.flat = (t10SG0 ++ t10SG1 ++ t10SG2) ++ ((t10SG3 ++ t10SG4 ++ t10SG5) ++
      ((t10SG6 ++ t10SG7 ++ t10SG8) ++ ((t10SG9 ++ t10SG10 ++ t10SG11)))) := by
    rw [t10V_flat]
    simp only [List.append_assoc]
  simp only [tv3pGT, tv3pGC, octChunkTerms_append, List.append_assoc]
  rw [hS]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv3pGT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv3pGT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv3pGT_g2
      tv3pGT_g3)))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
