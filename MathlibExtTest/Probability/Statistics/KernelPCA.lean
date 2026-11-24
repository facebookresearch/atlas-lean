/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.KernelPCA

@[expose] public section

/-!
# Tests for kernel principal component analysis
-/

set_option autoImplicit false

open Matrix
open MathlibExt.Probability.Statistics.KernelPCA
open MathlibExt.Probability.Statistics

namespace MathlibExtTest.Probability.Statistics.KernelPCA

/-- The Gram matrix of the identity feature map on `ℝ` at the two points `1, 1`. -/
theorem gram_ones : gram (fun t : ℝ => t) (fun _ : Fin 2 => (1 : ℝ)) = Matrix.of fun _ _ => 1 := by
  ext i j
  simp [KernelPCA.gram]

/-- Non-vacuity of the reduction: `α = (1, 1)` solves `M λ α = K α` with `M = 2`, `λ = 1`, so
`V = Φ(1) + Φ(1) = 2` is an eigenvector of the covariance operator with eigenvalue `1`. -/
example : covOp (fun t : ℝ => t) (fun _ : Fin 2 => (1 : ℝ))
      (expansion (fun t : ℝ => t) (fun _ : Fin 2 => (1 : ℝ)) fun _ => 1) =
    (1 : ℝ) • expansion (fun t : ℝ => t) (fun _ : Fin 2 => (1 : ℝ)) fun _ => 1 := by
  refine covOp_eq_smul_of_gram_mulVec_eq _ _ ?_
  rw [gram_ones]
  funext k
  simp [mulVec, dotProduct]

/-- The normalization (2.14) on the same example: `‖V‖² = M λ (α ⬝ α) = 2 · 2 = 4`. -/
example : ‖expansion (fun t : ℝ => t) (fun _ : Fin 2 => (1 : ℝ)) fun _ => 1‖ ^ 2 = 4 := by
  rw [norm_sq_expansion_of_gram_mulVec_eq (lam := 1) _ _]
  · simp [dotProduct]
    norm_num
  · rw [gram_ones]
    funext k
    simp [mulVec, dotProduct]

/-- The hypothesis `λ ≠ 0` of `mem_span_of_covOp_eq_smul` cannot be dropped: with no data
`C̄ = 0`, so `1` is an eigenvector for `λ = 0` although the span of the data is `{0}`. -/
example : covOp (fun t : ℝ => t) (fun i : Fin 0 => i.elim0) (1 : ℝ) = (0 : ℝ) • (1 : ℝ) := by
  simp [covOp]

/-- Centring on `ℝ`: the points `1, 3` have mean `2`, so the first centred feature is `-1`. -/
example : centredFeature (fun t : ℝ => t) ![(1 : ℝ), 3] 0 = -1 := by
  simp [centredFeature, Fin.sum_univ_two]
  norm_num

/-- The centred Gram matrix formula on the same data: `K̃₀₁ = ⟪-1, 1⟫ = -1`. -/
example : gram (centredFeature (fun t : ℝ => t) ![(1 : ℝ), 3]) id 0 1 = -1 := by
  simp [KernelPCA.gram, centredFeature, Fin.sum_univ_two]
  norm_num

end MathlibExtTest.Probability.Statistics.KernelPCA
