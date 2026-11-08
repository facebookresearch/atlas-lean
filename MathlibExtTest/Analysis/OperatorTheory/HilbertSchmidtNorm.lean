/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

/-- The zero operator has Hilbert–Schmidt norm `0`, in any family. -/
example (u : ℕ → ℝ) : hsENNNorm (0 : ℝ →L[ℝ] ℝ) u = 0 := by
  simp [hsENNNorm, hsNormSq]

/-- The identity against a constant unit family: the series of squares is the
constant series `∑' _ : ℕ, 1`, which diverges, so the norm is `⊤`, not `0`. -/
example : hsNormSq (ContinuousLinearMap.id ℝ ℝ) (fun _ : ℕ => (1 : ℝ)) = ⊤ := by
  simp only [hsNormSq, ContinuousLinearMap.id_apply, Real.norm_eq_abs,
    abs_one, one_pow, ENNReal.ofReal_one]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- Hence the extended Hilbert–Schmidt norm of the identity in that family
is `⊤` (the identity is not Hilbert–Schmidt), never `0` by divergence. -/
example : hsENNNorm (ContinuousLinearMap.id ℝ ℝ) (fun _ : ℕ => (1 : ℝ)) = ⊤ := by
  rw [hsENNNorm, show hsNormSq (ContinuousLinearMap.id ℝ ℝ) (fun _ : ℕ => (1 : ℝ)) = ⊤ from by
    simp only [hsNormSq, ContinuousLinearMap.id_apply, Real.norm_eq_abs,
      abs_one, one_pow, ENNReal.ofReal_one]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
  exact ENNReal.top_rpow_of_pos (by norm_num)

/-- A summable case: the identity against the family `1, 0, 0, …` has squared
norm `1`, hence norm `1`. -/
example : hsENNNorm (ContinuousLinearMap.id ℝ ℝ) (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) = 1 := by
  have hsq : hsNormSq (ContinuousLinearMap.id ℝ ℝ) (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) = 1 := by
    show (∑' n : ℕ, ENNReal.ofReal (‖if n = 0 then (1 : ℝ) else 0‖ ^ 2)) = 1
    rw [tsum_eq_single 0 (fun b hb => by simp [hb])]
    simp
  rw [hsENNNorm, hsq]
  simp

end MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm
