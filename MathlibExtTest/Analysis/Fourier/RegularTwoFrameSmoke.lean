/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import MathlibExt.Analysis.Fourier.RegularTwoFrame
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# A concrete regular real two-frame

With four columns, the zeroth and second columns are `(1/2,0)` and `(0,1/2)`.
The two row Gram values are `1/2`, the cross value is zero, and every column
has squared norm `1/4`. The one-column boundary instead has row Gram values
one and zero; the empty-column case is the zero frame.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RegularTwoFrameSmoke

private theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  have h : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [h, Real.sqrt_sq (by norm_num)]

private theorem first_cos : Real.regularTwoFrame 4 (0 : Fin 2) (0 : Fin 4) = 1 / 2 := by
  norm_num [Real.regularTwoFrame, sqrt_four]

private theorem first_sin : Real.regularTwoFrame 4 (1 : Fin 2) (0 : Fin 4) = 0 := by
  norm_num [Real.regularTwoFrame]

private theorem quarter_cos : Real.regularTwoFrame 4 (0 : Fin 2) (2 : Fin 4) = 0 := by
  change Real.cos (Real.pi * 2 / 4) / Real.sqrt 4 = 0
  rw [show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two, zero_div]

private theorem quarter_sin : Real.regularTwoFrame 4 (1 : Fin 2) (2 : Fin 4) = 1 / 2 := by
  change Real.sin (Real.pi * 2 / 4) / Real.sqrt 4 = 1 / 2
  rw [show Real.pi * 2 / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two, sqrt_four]

example : Real.regularTwoFrame 4 (0 : Fin 2) (0 : Fin 4) = 1 / 2 ∧
    Real.regularTwoFrame 4 (1 : Fin 2) (0 : Fin 4) = 0 ∧
    Real.regularTwoFrame 4 (0 : Fin 2) (2 : Fin 4) = 0 ∧
    Real.regularTwoFrame 4 (1 : Fin 2) (2 : Fin 4) = 1 / 2 ∧
    Real.regularTwoFrame 4 ≠ 0 := by
  refine ⟨first_cos, first_sin, quarter_cos, quarter_sin, ?_⟩
  intro hzero
  have h := congrArg (fun F : Fin 2 → Fin 4 → ℝ => F 0 0) hzero
  rw [first_cos] at h
  norm_num at h

example :
    (∑ j : Fin 4, Real.regularTwoFrame 4 0 j * Real.regularTwoFrame 4 0 j) = 1 / 2 ∧
    (∑ j : Fin 4, Real.regularTwoFrame 4 0 j * Real.regularTwoFrame 4 1 j) = 0 ∧
    (∑ j : Fin 4, Real.regularTwoFrame 4 1 j * Real.regularTwoFrame 4 1 j) = 1 / 2 ∧
    (∑ r : Fin 2, (Real.regularTwoFrame 4 r (2 : Fin 4)) ^ 2) = 1 / 4 := by
  have h00 := Real.regularTwoFrame_gram 4 (by decide) (0 : Fin 2) 0
  have h01 := Real.regularTwoFrame_gram 4 (by decide) (0 : Fin 2) 1
  have h11 := Real.regularTwoFrame_gram 4 (by decide) (1 : Fin 2) 1
  norm_num at h00 h01 h11
  exact ⟨h00, h01, h11, Real.regularTwoFrame_row_norm 4 (by decide) (2 : Fin 4)⟩

example : Real.regularTwoFrame 1 (0 : Fin 2) (0 : Fin 1) = 1 ∧
    Real.regularTwoFrame 1 (1 : Fin 2) (0 : Fin 1) = 0 ∧
    (∑ j : Fin 1, Real.regularTwoFrame 1 0 j * Real.regularTwoFrame 1 0 j) = 1 ∧
    (∑ j : Fin 1, Real.regularTwoFrame 1 1 j * Real.regularTwoFrame 1 1 j) = 0 := by
  norm_num [Real.regularTwoFrame, Fin.sum_univ_one]

example : Real.regularTwoFrame 0 = 0 ∧
    (∑ j : Fin 0, Real.regularTwoFrame 0 0 j * Real.regularTwoFrame 0 0 j) = 0 :=
  ⟨Subsingleton.elim _ _, by simp⟩

end RegularTwoFrameSmoke
