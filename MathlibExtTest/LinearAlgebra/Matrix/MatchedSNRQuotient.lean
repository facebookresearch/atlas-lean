/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
open scoped Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.MatchedSNRQuotient

/-- The leaf's validation case: `R = diag(1, 4)`, `s = w = 1`
gives SNR `4/5`. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 1] ![1, 1] = 4 / 5 :=
  diag_one_four_matchedSNR_ones

/-- Zero signal has zero SNR for a nonzero weight. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    0 ![1, 0] = 0 :=
  matchedSNR_zero_signal _ _ (by
    intro h
    have h0 := congrFun h 0
    simp at h0)

/-- The headline bound on the validation matrix with the
non-optimal weight `w = (1, 0)`. -/
example : matchedSNR (Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 1] ![1, 0]
    ≤ dotProduct ![1, 1] ((Matrix.diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      *ᵥ ![1, 1]) :=
  matchedSNR_le_dotProduct_inv_mulVec _ diag_one_four_posDef _ _
    (by
      intro h
      have h0 := congrFun h 0
      simp at h0)
    (by
      intro h
      have h0 := congrFun h 0
      simp at h0)

end MathlibExtTest.LinearAlgebra.Matrix.MatchedSNRQuotient
