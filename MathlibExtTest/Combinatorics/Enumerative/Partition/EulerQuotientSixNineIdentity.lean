/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientSixNineIdentity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

open MetaMathlibExt QPochhammer

-- When the three denominators do not vanish, the identity clears to the polynomial relation
-- E₆⁸ E₉⁴ E₁₈ = E₃ E₆³ E₉⁹ + q³ E₃⁴ E₁₈⁹ between the Euler products.
example (q : ℂ) (hq : ‖q‖ < 1) (h₃ : ‖q ^ 3‖ < 1) (h₆ : ‖q ^ 6‖ < 1) (h₉ : ‖q ^ 9‖ < 1)
    (h₁₈ : ‖q ^ 18‖ < 1) (n₃ : qPochhammerInf (q ^ 3) (q ^ 3) h₃ ≠ 0)
    (n₉ : qPochhammerInf (q ^ 9) (q ^ 9) h₉ ≠ 0)
    (n₁₈ : qPochhammerInf (q ^ 18) (q ^ 18) h₁₈ ≠ 0) :
    qPochhammerInf (q ^ 6) (q ^ 6) h₆ ^ 8 * qPochhammerInf (q ^ 9) (q ^ 9) h₉ ^ 4 *
        qPochhammerInf (q ^ 18) (q ^ 18) h₁₈ =
      qPochhammerInf (q ^ 3) (q ^ 3) h₃ * qPochhammerInf (q ^ 6) (q ^ 6) h₆ ^ 3 *
          qPochhammerInf (q ^ 9) (q ^ 9) h₉ ^ 9 +
        q ^ 3 * qPochhammerInf (q ^ 3) (q ^ 3) h₃ ^ 4 *
          qPochhammerInf (q ^ 18) (q ^ 18) h₁₈ ^ 9 := by
  have h := eulerFunction_six_cube_nine_six_div_eq q hq
  simp only [OfNat.ofNat_ne_zero, ↓reduceDIte] at h
  field_simp at h
  linear_combination -h

-- The hypothesis is satisfiable: the identity holds at q = 1/2.
example :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      qPochhammerInf ((1 / 2 : ℂ) ^ k) ((1 / 2 : ℂ) ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (by norm_num) hk)
    E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) =
      E 6 ^ 8 * E 9 / (E 3 ^ 4 * E 18 ^ 2) - (1 / 2 : ℂ) ^ 3 * (E 18 ^ 6 / E 9 ^ 3) :=
  eulerFunction_six_cube_nine_six_div_eq (1 / 2) (by norm_num)
