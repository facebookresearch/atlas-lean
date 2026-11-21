/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrum

@[expose] public section

open scoped Matrix
open MathlibExt.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrum

namespace MathlibExtTest.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrumTests

/-- The two-vertex half path Laplacian in coordinates. -/
theorem halfPathLaplacian_two :
    halfPathLaplacian 2 =
      Matrix.of !![(1 / 2 : ℝ), -(1 / 2 : ℝ); -(1 / 2 : ℝ), (1 / 2 : ℝ)] := by
  have d0 : (SimpleGraph.pathGraph 2).degree 0 = 1 := by decide
  have d1 : (SimpleGraph.pathGraph 2).degree 1 = 1 := by decide
  have a01 : (SimpleGraph.pathGraph 2).Adj 0 1 := by decide
  have a10 : (SimpleGraph.pathGraph 2).Adj 1 0 := by decide
  have fin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    have hv : i.val = 0 ∨ i.val = 1 := by have h := i.isLt; omega
    rcases hv with hv | hv
    · left; exact Fin.ext hv
    · right; exact Fin.ext hv
  ext i j
  rcases fin2 i with rfl | rfl <;> rcases fin2 j with rfl | rfl <;>
    simp [halfPathLaplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, d0,
      d1, a01, a10] <;>
    rfl

/-- Zero is an eigenvalue in dimension two. -/
theorem zero_eigenvalue_two :
    ∃ v ≠ 0, halfPathLaplacian 2 *ᵥ v = (0 : ℝ) • v := by
  refine ⟨pathCosineMode 2 0, pathCosineMode_ne_zero (by norm_num), ?_⟩
  have h := halfPathLaplacian_mulVec_pathCosineMode (n := 2) (by norm_num) 0
  simpa using h

/-- One is an eigenvalue in dimension two. -/
theorem one_eigenvalue_two :
    ∃ v ≠ 0, halfPathLaplacian 2 *ᵥ v = (1 : ℝ) • v := by
  refine ⟨pathCosineMode 2 1, pathCosineMode_ne_zero (by norm_num), ?_⟩
  have h := halfPathLaplacian_mulVec_pathCosineMode (n := 2) (by norm_num) 1
  have harg : Real.pi * ((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = Real.pi / 2 := by
    norm_num
  rw [harg, Real.cos_pi_div_two] at h
  simpa using h

/-- The zeroth cosine mode is constant. -/
theorem pathCosineMode_zero (n : ℕ) :
    pathCosineMode n 0 = fun _ => 1 := by
  funext j
  simp [pathCosineMode, Real.cos_zero]

/-- The zeroth cosine mode lies in the kernel. -/
theorem halfPathLaplacian_mulVec_pathCosineMode_zero {n : ℕ} (hn : 0 < n) :
    halfPathLaplacian n *ᵥ pathCosineMode n 0 = 0 := by
  have h := halfPathLaplacian_mulVec_pathCosineMode hn 0
  simpa using h

/-- The first mode in dimension three satisfies its eigen-equation. -/
example :
    halfPathLaplacian 3 *ᵥ pathCosineMode 3 1 =
      (1 - Real.cos (Real.pi / 3)) • pathCosineMode 3 1 := by
  have h := halfPathLaplacian_mulVec_pathCosineMode (n := 3) (by norm_num) 1
  have harg : Real.pi * ((1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) = Real.pi / 3 := by
    norm_num
  rwa [harg] at h

#print axioms halfPathLaplacian_mulVec_pathCosineMode
#print axioms pathCosineMode_ne_zero
#print axioms pathCosineMode_dotProduct_eq_zero
#print axioms halfPathLaplacian_hasEigenvalue_iff
#print axioms halfPathLaplacian_quadForm_ge
#print axioms halfPathLaplacian_eigenvalue_ge
#print axioms two_div_sq_le_one_sub_cos_pi_div
#print axioms propagation_gap_ge

end MathlibExtTest.Combinatorics.SimpleGraph.PathGraphLaplacianSpectrumTests
