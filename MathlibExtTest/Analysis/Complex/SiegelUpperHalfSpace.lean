/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.SiegelUpperHalfSpace

open Matrix

namespace Siegel

-- `i` (as a `1 × 1` matrix) lies in `𝔖_1`.
example : !![Complex.I] ∈ upperHalfSpace 1 := by
  rw [mem_upperHalfSpace_one_iff]
  simp

-- `-i` does not.
example : !![-Complex.I] ∉ upperHalfSpace 1 := by
  rw [mem_upperHalfSpace_one_iff]
  simp

-- `J = (0 1; -1 0)` lies in `Sp_{2g}(ℤ)`, for every `g`.
example (g : ℕ) : J g ∈ Sp g := by
  rw [mem_Sp_iff_mem_symplecticGroup, J_eq_neg]
  exact SymplecticGroup.neg_mem (SymplecticGroup.J_mem _ _)

-- Condition S. 3 holds for every `1 × 1` matrix.
example (τ : Matrix (Fin 1) (Fin 1) ℂ) : SiegelS3 τ := siegelS3_of_eq_one τ

-- Condition S. 2 for `i`: the real part is `0`.
example : SiegelS2 !![Complex.I] := by
  intro i j
  fin_cases i; fin_cases j
  norm_num

end Siegel
