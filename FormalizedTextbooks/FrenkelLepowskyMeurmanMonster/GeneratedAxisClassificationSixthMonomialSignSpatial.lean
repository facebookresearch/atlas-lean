/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpatialStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionCode

/-! Genuine equal-sign monomial generators preserve the literal sixth rooted-plane matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Ten literal source-code labels satisfying the three-coordinate equal-sign conditions. -/
def generatedSixthMonomialSignCode : Fin 10 → Fin 4096 :=
  ![1, 2, 4, 8, 96, 176, 304, 528, 1056, 2048]

/-- All ten genuine Golay codewords have equal bits on the three distinguished coordinates. -/
theorem generatedSixth_monomial_sign_code_certificate : ∀ j : Fin 10,
    golayEncoder (golayLabelCoefficients (generatedSixthMonomialSignCode j)) 17 =
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialSignCode j)) 16 ∧
    golayEncoder (golayLabelCoefficients (generatedSixthMonomialSignCode j)) 19 =
      golayEncoder (golayLabelCoefficients (generatedSixthMonomialSignCode j)) 16 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Only the 576 sparse rational matrix entries and their binary coordinate signs are checked.
/-- Equal signs on the three genuine root coordinates preserve the exact original axis matrix. -/
theorem generatedSixth_equal_signs_spatial (d : Fin 4096)
    (h17 : golayEncoder (golayLabelCoefficients d) 17 =
      golayEncoder (golayLabelCoefficients d) 16)
    (h19 : golayEncoder (golayLabelCoefficients d) 19 =
      golayEncoder (golayLabelCoefficients d) 16) :
    golaySignIsometry (sourceGeneratedSignCode d) ∈ generatedSixthSpatialStabilizer := by
  change conwayMatrixAction _ (griessConwayEncode generatedSixthAxis).1 = _
  rw [generatedSixth_axis_matrix]
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [generatedSixthAxisMatrix, generatedSixthMiddlePairValue,
      h17, h19, ZModModule.add_self, qSign_zero]

/-- Each literal source sign generator belongs to the actual counted spatial flag stabilizer. -/
theorem generatedSixth_monomial_sign_spatial_mem (j : Fin 10) :
    golaySignIsometry (sourceGeneratedSignCode (generatedSixthMonomialSignCode j)) ∈
      generatedSixthSpatialStabilizer :=
  generatedSixth_equal_signs_spatial _
    (generatedSixth_monomial_sign_code_certificate j).1
    (generatedSixth_monomial_sign_code_certificate j).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
