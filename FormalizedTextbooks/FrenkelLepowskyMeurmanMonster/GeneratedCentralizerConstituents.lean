/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic separation of the actual symmetric-matrix and short-vector constituents. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerNormIdentities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTraceBridge

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The actual tensor trace has the exact source norm coefficients on the fixed eigenspace. -/
theorem generatedCentralTensorTraceForm_self (x : generatedCentralPlus) :
    generatedCentralTensorTraceForm x x =
      4096 * generatedCentralMatrixNormSq x +
      2560 * ((generatedCentralPlusCoordinates x).1.val.trace) ^ 2 +
      4608 * generatedCentralShortNormSq x := by
  have h := generatedCentralTensorTraceForm_coordinates x x
  have hc := generatedCentral_coordinate_trace_norm x
  rw [centralizerCoordinateTensorMul_trace_comp] at hc
  simp only [generatedCentralPlusCoordinates_fst_val, generatedCentralPlusCoordinates_snd] at hc
  exact h.trans hc

/-- The two actual preserved forms determine the short-coordinate square norm intrinsically. -/
theorem generatedCentralizer_preserves_short_norm (g : generatedCentralizer)
    (x : generatedCentralPlus) :
    generatedCentralShortNormSq (generatedCentralizerPlusEquiv g x) =
      generatedCentralShortNormSq x := by
  have ht := generatedCentralizer_preserves_tensorTraceForm g x x
  rw [generatedCentralTensorTraceForm_self, generatedCentralTensorTraceForm_self,
    generatedCentralizer_preserves_matrix_trace] at ht
  have hn := generated_group_preserves_griessForm g.val x.val x.val
  change griessForm (generatedCentralizerPlusEquiv g x).val
    (generatedCentralizerPlusEquiv g x).val = griessForm x.val x.val at hn
  rw [generatedCentralPlus_form_self, generatedCentralPlus_form_self] at hn
  linarith

/-- Every element of the full actual centralizer preserves the matrix constituent. -/
theorem generatedCentralizer_preserves_matrix (g : generatedCentralizer)
    (x : generatedCentralPlus) (hx : x ∈ generatedCentralMatrix) :
    generatedCentralizerPlusEquiv g x ∈ generatedCentralMatrix := by
  apply (generatedCentralShortNormSq_eq_zero_iff _).mp
  rw [generatedCentralizer_preserves_short_norm]
  exact (generatedCentralShortNormSq_eq_zero_iff x).mpr hx

/-- The same intrinsic forms force preservation of the actual short-vector constituent. -/
theorem generatedCentralizer_preserves_short (g : generatedCentralizer)
    (x : generatedCentralPlus) (hx : x ∈ generatedCentralShort) :
    generatedCentralizerPlusEquiv g x ∈ generatedCentralShort := by
  apply (generatedCentralMatrixNormSq_eq_zero_iff _).mp
  have hm := (generatedCentralMatrixNormSq_eq_zero_iff x).mpr hx
  have hn := generated_group_preserves_griessForm g.val x.val x.val
  change griessForm (generatedCentralizerPlusEquiv g x).val
    (generatedCentralizerPlusEquiv g x).val = griessForm x.val x.val at hn
  rw [generatedCentralPlus_form_self, generatedCentralPlus_form_self,
    generatedCentralizer_preserves_short_norm, hm] at hn
  linarith

/-- Restrict an actual centralizer element to its now intrinsically preserved matrix space. -/
noncomputable def generatedCentralizerMatrixEquiv (g : generatedCentralizer) :
    generatedCentralMatrix ≃ₗ[ℝ] generatedCentralMatrix where
  toFun x := ⟨generatedCentralizerPlusEquiv g x.val,
    generatedCentralizer_preserves_matrix g x.val x.property⟩
  invFun x := ⟨generatedCentralizerPlusEquiv g⁻¹ x.val,
    generatedCentralizer_preserves_matrix g⁻¹ x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact g.val.val.symm_apply_apply x.val.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact g.val.val.apply_symm_apply x.val.val
  map_add' x y := Subtype.ext ((generatedCentralizerPlusEquiv g).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((generatedCentralizerPlusEquiv g).map_smul c x.val)

/-- Restrict that same actual centralizer element to the intrinsically preserved short space. -/
noncomputable def generatedCentralizerShortEquiv (g : generatedCentralizer) :
    generatedCentralShort ≃ₗ[ℝ] generatedCentralShort where
  toFun x := ⟨generatedCentralizerPlusEquiv g x.val,
    generatedCentralizer_preserves_short g x.val x.property⟩
  invFun x := ⟨generatedCentralizerPlusEquiv g⁻¹ x.val,
    generatedCentralizer_preserves_short g⁻¹ x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact g.val.val.symm_apply_apply x.val.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact g.val.val.apply_symm_apply x.val.val
  map_add' x y := Subtype.ext ((generatedCentralizerPlusEquiv g).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((generatedCentralizerPlusEquiv g).map_smul c x.val)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
