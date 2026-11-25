/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqNormProduct

/-!
# Tests for the Gaussian norm products on `C₄ × C₄`
-/

namespace MetaMathlibExt.C4SqNormProductTest

private def sample (p : Fin 4 × Fin 4) : ℤ :=
  ![![1, 2, 0, 0], ![-1, 1, 0, 0], ![2, -1, 0, 0], ![1, 3, 0, 0]] p.1 p.2

-- The squared lengths of the four Gaussian factors are 34, 18, 2 and 34.
example : (c4SqBeta sample).norm = 34 * 18 ∧ (c4SqGamma sample).norm = 2 * 34 := by
  obtain ⟨hβ, hγ⟩ := c4Sq_norm_beta_gamma_eq sample
  exact ⟨hβ.trans (by decide), hγ.trans (by decide)⟩

-- With α₀ = 1 and α₁ = i, one of the factors of γ vanishes.
example :
    let a (p : Fin 4 × Fin 4) : ℤ := if p = (0, 0) ∨ p = (1, 1) then 1 else 0
    (c4SqBeta a).norm = 4 ∧ (c4SqGamma a).norm = 0 := by
  intro a
  obtain ⟨hβ, hγ⟩ := c4Sq_norm_beta_gamma_eq a
  exact ⟨hβ.trans (by decide +revert), hγ.trans (by decide +revert)⟩

end MetaMathlibExt.C4SqNormProductTest
