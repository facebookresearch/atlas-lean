/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqNormDifference

/-!
# Tests for the difference of the Gaussian norms on `C₄ × C₄`
-/

namespace MetaMathlibExt.C4SqNormDifference

-- The three nonzero entries give α₀ = 1 + i and α₂ = -i.
private def sample (p : Fin 4 × Fin 4) : ℤ :=
  if p = (0, 0) ∨ p = (0, 1) ∨ p = (2, 3) then 1 else 0

example : c4SqAlpha sample = ![⟨1, 1⟩, 0, ⟨0, -1⟩, 0] := by decide

example : c4SqBeta sample = 1 ∧ c4SqGamma sample = ⟨-3, 4⟩ := by decide

-- The norm difference is -24, and the row products give 8.
example : (c4SqBeta sample).norm - (c4SqGamma sample).norm ≡ 8 [ZMOD 16] :=
  (c4Sq_norm_beta_sub_norm_gamma_mod_sixteen sample (by decide)).trans (by decide)

-- With equal parity the congruence can fail: β = 0, γ = 2 and the row products vanish.
example :
    let a (p : Fin 4 × Fin 4) : ℤ := if p = (0, 0) ∨ p = (1, 0) then 1 else 0
    c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2] ∧
      ¬ (c4SqBeta a).norm - (c4SqGamma a).norm ≡
        4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
          c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16] := by
  decide

end MetaMathlibExt.C4SqNormDifference
