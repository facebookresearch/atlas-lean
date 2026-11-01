/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthV59pData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthSrcS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthOddChunks

/-! # Short transport check of the Tenth identification T59+ (H side)

Group by group (twelve groups of `4096` terms of the scaled Tenth source short block). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of flat group 0 (H). -/
theorem tv59pHT_g0 : shortCheckF tv59pHD t10SG0 (OctadDense.octChunkTerms tv59pHC0) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 1 (H). -/
theorem tv59pHT_g1 : shortCheckF tv59pHD t10SG1 (OctadDense.octChunkTerms tv59pHC1) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 2 (H). -/
theorem tv59pHT_g2 : shortCheckF tv59pHD t10SG2 (OctadDense.octChunkTerms tv59pHC2) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 3 (H). -/
theorem tv59pHT_g3 : shortCheckF tv59pHD t10SG3 (OctadDense.octChunkTerms tv59pHC3) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 4 (H). -/
theorem tv59pHT_g4 : shortCheckF tv59pHD t10SG4 (OctadDense.octChunkTerms tv59pHC4) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 5 (H). -/
theorem tv59pHT_g5 : shortCheckF tv59pHD t10SG5 (OctadDense.octChunkTerms tv59pHC5) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 6 (H). -/
theorem tv59pHT_g6 : shortCheckF tv59pHD t10SG6 (OctadDense.octChunkTerms tv59pHC6) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 7 (H). -/
theorem tv59pHT_g7 : shortCheckF tv59pHD t10SG7 (OctadDense.octChunkTerms tv59pHC7) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 8 (H). -/
theorem tv59pHT_g8 : shortCheckF tv59pHD t10SG8 (OctadDense.octChunkTerms tv59pHC8) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 9 (H). -/
theorem tv59pHT_g9 : shortCheckF tv59pHD t10SG9 (OctadDense.octChunkTerms tv59pHC9) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 10 (H). -/
theorem tv59pHT_g10 : shortCheckF tv59pHD t10SG10 (OctadDense.octChunkTerms tv59pHC10) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 11 (H). -/
theorem tv59pHT_g11 : shortCheckF tv59pHD t10SG11 (OctadDense.octChunkTerms tv59pHC11) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The short block of the H image is the checked transport of the scaled Tenth source short
block. -/
theorem tv59pHT_check : shortCheckF tv59pHD t10V.sh.flat tv59pHT = true := by
  rw [t10V_flat]
  simp only [tv59pHT, tv59pHC, octChunkTerms_append, List.append_assoc]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g2
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g3
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g4
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g5
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g6
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g7
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g8
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g9
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pHT_g10
      tv59pHT_g11)))))))))))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
