/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Pythagoras for finitely many pairwise-orthogonal vectors

For a finite family of pairwise-orthogonal vectors `v : ι → E` in an inner product space
over an `RCLike` field `𝕜` such as `ℝ` or `ℂ`, the squared norm of the sum is the sum of
the squared norms. This extends Mathlib's two-vector identity
`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero` to finitely many vectors.
-/

@[expose] public section

open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.FinitePythagoras

variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for finitely many vectors**: if the vectors `v i` are pairwise orthogonal,
the squared norm of their sum is the sum of their squared norms. -/
theorem norm_sum_sq_eq_sum_norm_sq (v : ι → E)
    (horth : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have hinner : ⟪∑ i, v i, ∑ j, v j⟫_𝕜 = ∑ i, ⟪v i, v i⟫_𝕜 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => horth (Ne.symm hji))
      (fun hi => absurd (Finset.mem_univ i) hi)
  simp only [inner_self_eq_norm_sq_to_K] at hinner
  exact_mod_cast hinner

/-- If pairwise-orthogonal vectors sum to a unit vector, their squared norms sum to `1`. -/
theorem sum_norm_sq_eq_one_of_norm_sum_eq_one (v : ι → E)
    (horth : Pairwise fun i j => ⟪v i, v j⟫_𝕜 = 0) (hunit : ‖∑ i, v i‖ = 1) :
    ∑ i, ‖v i‖ ^ 2 = 1 := by
  rw [← norm_sum_sq_eq_sum_norm_sq v horth, hunit, one_pow]

end MathlibExt.Analysis.InnerProductSpace.FinitePythagoras

end
