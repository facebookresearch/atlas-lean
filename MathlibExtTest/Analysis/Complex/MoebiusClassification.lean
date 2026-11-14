/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.MoebiusClassification

set_option autoImplicit false

open Matrix Moebius

-- The translation `z ↦ z + 1` is parabolic: `tr ^ 2 - 4 * det = 4 - 4 = 0`.
example : IsParabolic (GeneralLinearGroup.mkOfDetNeZero !![(1 : ℂ), 1; 0, 1] (by simp)) := by
  rw [isParabolic_iff_discr_eq_zero]
  norm_num [discr_fin_two, trace_fin_two, det_fin_two]

-- The dilation `z ↦ 2 * z` is strictly hyperbolic (`tr ^ 2 / det = 9 / 2 > 4`) and not
-- parabolic (`tr ^ 2 - 4 * det = 1`).
example :
    IsStrictlyHyperbolic (GeneralLinearGroup.mkOfDetNeZero !![(2 : ℂ), 0; 0, 1] (by simp)) ∧
      ¬IsParabolic (GeneralLinearGroup.mkOfDetNeZero !![(2 : ℂ), 0; 0, 1] (by simp)) := by
  rw [isStrictlyHyperbolic_iff_trace_sq_div_det, isParabolic_iff_discr_eq_zero]
  refine ⟨⟨9 / 2, by norm_num, ?_⟩, ?_⟩ <;>
    norm_num [discr_fin_two, trace_fin_two, det_fin_two]

-- The rotation `z ↦ I * z` is elliptic: `tr ^ 2 / det = (I + 1) ^ 2 / I = 2`.
example : IsElliptic (GeneralLinearGroup.mkOfDetNeZero !![Complex.I, 0; 0, 1] (by simp)) := by
  rw [isElliptic_iff_trace_sq_div_det]
  refine ⟨2, by norm_num, by norm_num, ?_⟩
  simp only [GeneralLinearGroup.val_mkOfDetNeZero, trace_fin_two_of, det_fin_two_of]
  rw [div_eq_iff (by simp)]
  push_cast
  linear_combination Complex.I_sq

#print axioms classification_by_trace
