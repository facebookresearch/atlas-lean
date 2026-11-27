/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.RankProduct

-- The middle dimension can be zero even if both outer dimensions are nonzero.
example {K : Type*} [Field K] (A : Matrix (Fin 2) (Fin 0) K)
    (B : Matrix (Fin 0) (Fin 3) K) : (A * B).rank = 0 := by
  obtain ⟨hprod, hwidth⟩ := Matrix.rank_mul_le_min_and_min_le_width A B
  exact Nat.eq_zero_of_le_zero (hprod.trans hwidth)
