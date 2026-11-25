/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNorm

open MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

namespace MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (u : HilbertBasis ℕ ℝ H)

/-- The rank-one projection onto a basis vector attains the bound at that vector. -/
example (k : ℕ) :
    ENNReal.ofReal ‖InnerProductSpace.rankOne ℝ (u k) (u k) (u k)‖ =
      hsENNNorm (InnerProductSpace.rankOne ℝ (u k) (u k)) u := by
  apply le_antisymm
  · exact norm_apply_le_hsNorm_of_norm_eq_one H _ u _ (u.orthonormal.norm_eq_one k)
  · have hinner := orthonormal_iff_ite.mp u.orthonormal
    simp only [hsENNNorm, hsNormSq, InnerProductSpace.rankOne_apply, hinner]
    rw [tsum_eq_single k (fun i hi => by simp [Ne.symm hi])]
    simp [u.orthonormal.norm_eq_one]

/-- The identity has infinite Hilbert–Schmidt norm in a countably infinite Hilbert basis. -/
example : hsENNNorm (ContinuousLinearMap.id ℝ H) u = ⊤ := by
  simp [hsENNNorm, hsNormSq, u.orthonormal.norm_eq_one]

end MathlibExt.Analysis.OperatorTheory.NormApplyLeHilbertSchmidtNormWanted
