/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetryExistsReverseSymmetricDensityNeGaussKuzmin

namespace MathlibExtTest.NumberTheory.GaussKuzminSymmetryExistsReverseSymmetricDensityNeGaussKuzmin

-- At `N = 1`, project out the nonnegativity and the disagreement with the Gauss–Kuzmin density.
example : ∃ f : ℝ → ℝ, (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) ∧
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 1 / (Real.log 2 * (1 + x)) := by
  obtain ⟨f, -, hf0, -, -, hne⟩ :=
    MetaMathlibExt.exists_reverse_symmetric_density_ne_gaussKuzmin 1 le_rfl
  exact ⟨f, hf0, hne⟩

-- At `N = 2`, the witness is symmetric on the concrete non-palindromic string `[1, 2]`.
example : ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧
    ∫ x in MetaMathlibExt.cfCylinder [1, 2], f x =
      ∫ x in MetaMathlibExt.cfCylinder [2, 1], f x := by
  obtain ⟨f, hfC, -, -, hsym, -⟩ :=
    MetaMathlibExt.exists_reverse_symmetric_density_ne_gaussKuzmin 2 (by norm_num)
  refine ⟨f, hfC, ?_⟩
  have h := hsym [1, 2] (by decide) (by decide)
  have hrev : [1, 2].reverse = [2, 1] := rfl
  rw [hrev] at h
  exact h

end MathlibExtTest.NumberTheory.GaussKuzminSymmetryExistsReverseSymmetricDensityNeGaussKuzmin
