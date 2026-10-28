/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthF64pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the Tenth identification T64+ (H side)

Group by group (groups of `12288` terms of the scaled Tenth source short block). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of group 0 (H). -/
theorem tf64pHT_g0 :
    shortCheckF tf64pHD (t10SG0 ++ t10SG1 ++ t10SG2)
      (OctadDense.octChunkTerms tf64pHC0) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 1 (H). -/
theorem tf64pHT_g1 :
    shortCheckF tf64pHD (t10SG3 ++ t10SG4 ++ t10SG5)
      (OctadDense.octChunkTerms tf64pHC1) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 2 (H). -/
theorem tf64pHT_g2 :
    shortCheckF tf64pHD (t10SG6 ++ t10SG7 ++ t10SG8)
      (OctadDense.octChunkTerms tf64pHC2) = true :=
  shortCheckPk_sound _ 10 13 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of group 3 (H). -/
theorem tf64pHT_g3 :
    shortCheckF tf64pHD (t10SG9 ++ t10SG10 ++ t10SG11)
      (OctadDense.octChunkTerms tf64pHC3) = true :=
  shortCheckPk_sound _ 10 10 _ _ (by decide +kernel)

/-- The short block of the H image is the checked transport of the scaled Tenth source short
block. -/
theorem tf64pHT_check : shortCheckF tf64pHD t10V.sh.flat tf64pHT = true := by
  have hS : t10V.sh.flat = (t10SG0 ++ t10SG1 ++ t10SG2) ++ ((t10SG3 ++ t10SG4 ++ t10SG5) ++
      ((t10SG6 ++ t10SG7 ++ t10SG8) ++ ((t10SG9 ++ t10SG10 ++ t10SG11)))) := by
    rw [t10V_flat]
    simp only [List.append_assoc]
  simp only [tf64pHT, tf64pHC, octChunkTerms_append, List.append_assoc]
  rw [hS]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) tf64pHT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tf64pHT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tf64pHT_g2
      tf64pHT_g3)))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
