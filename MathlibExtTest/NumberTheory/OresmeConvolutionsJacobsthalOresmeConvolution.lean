/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.OresmeConvolutionsJacobsthalOresmeConvolution

/-! # Tests for the Jacobsthal–Oresme convolution -/

namespace MathlibExtTest.NumberTheory.OresmeConvolutionsJacobsthalOresmeConvolution

open MetaMathlibExt

-- The Oresme factor `0 / 2 ^ 0` makes the initial convolution vanish, although `J₁ = 1`.
example : ∑ k ∈ Finset.range 1,
    (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((0 - k : ℕ) : ℚ) / 2 ^ (0 - k)) = 0 := by
  rw [jacobsthal_oresme_convolution 0]
  norm_num [lucasU]

-- At index four the convolution is `3 / 8 + 1 / 2 + 3 / 2 = 19 / 8`.
example : ∑ k ∈ Finset.range 5,
    (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((4 - k : ℕ) : ℚ) / 2 ^ (4 - k)) = 19 / 8 := by
  rw [jacobsthal_oresme_convolution 4]
  norm_num [lucasU]

-- Clearing denominators gives `9 * 2 ^ n * ∑ J_k O_{n-k} = 2 ^ (n+1) * J_{n+1} - 2 * (n+1)`.
example (n : ℕ) :
    9 * 2 ^ n * ∑ k ∈ Finset.range (n + 1),
        (lucasU ⟨1, -2, by decide⟩ k : ℚ) * (((n - k : ℕ) : ℚ) / 2 ^ (n - k)) =
      2 ^ (n + 1) * (lucasU ⟨1, -2, by decide⟩ (n + 1) : ℚ) - 2 * ((n : ℚ) + 1) := by
  rw [jacobsthal_oresme_convolution]
  field_simp
  ring

end MathlibExtTest.NumberTheory.OresmeConvolutionsJacobsthalOresmeConvolution
