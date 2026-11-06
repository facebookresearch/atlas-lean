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

/-! # Short transport check of the Tenth identification T59+ (G side)

Group by group (twelve groups of `4096` terms of the scaled Tenth source short block). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- Transport check of flat group 0 (G). -/
theorem tv59pGT_g0 : shortCheckF tv59pGD t10SG0 (OctadDense.octChunkTerms tv59pGC0) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 1 (G). -/
theorem tv59pGT_g1 : shortCheckF tv59pGD t10SG1 (OctadDense.octChunkTerms tv59pGC1) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 2 (G). -/
theorem tv59pGT_g2 : shortCheckF tv59pGD t10SG2 (OctadDense.octChunkTerms tv59pGC2) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 3 (G). -/
theorem tv59pGT_g3 : shortCheckF tv59pGD t10SG3 (OctadDense.octChunkTerms tv59pGC3) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 4 (G). -/
theorem tv59pGT_g4 : shortCheckF tv59pGD t10SG4 (OctadDense.octChunkTerms tv59pGC4) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 5 (G). -/
theorem tv59pGT_g5 : shortCheckF tv59pGD t10SG5 (OctadDense.octChunkTerms tv59pGC5) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 6 (G). -/
theorem tv59pGT_g6 : shortCheckF tv59pGD t10SG6 (OctadDense.octChunkTerms tv59pGC6) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 7 (G). -/
theorem tv59pGT_g7 : shortCheckF tv59pGD t10SG7 (OctadDense.octChunkTerms tv59pGC7) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 8 (G). -/
theorem tv59pGT_g8 : shortCheckF tv59pGD t10SG8 (OctadDense.octChunkTerms tv59pGC8) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 9 (G). -/
theorem tv59pGT_g9 : shortCheckF tv59pGD t10SG9 (OctadDense.octChunkTerms tv59pGC9) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 10 (G). -/
theorem tv59pGT_g10 : shortCheckF tv59pGD t10SG10 (OctadDense.octChunkTerms tv59pGC10) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Transport check of flat group 11 (G). -/
theorem tv59pGT_g11 : shortCheckF tv59pGD t10SG11 (OctadDense.octChunkTerms tv59pGC11) =
    true :=
  shortCheckPk_sound _ 10 5 _ _ (by decide +kernel)

/-- The short block of the G image is the checked transport of the scaled Tenth source short
block. -/
theorem tv59pGT_check : shortCheckF tv59pGD t10V.sh.flat tv59pGT = true := by
  rw [t10V_flat]
  simp only [tv59pGT, tv59pGC, octChunkTerms_append, List.append_assoc]
  exact (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g0
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g1
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g2
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g3
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g4
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g5
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g6
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g7
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g8
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g9
      (shortCheckF_append _ _ _ _ _ (by decide +kernel) tv59pGT_g10
      tv59pGT_g11)))))))))))

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
