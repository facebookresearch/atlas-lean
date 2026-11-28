/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.LucasBinomialCatalanConvolution

/-! # Tests for the binomial-Catalan convolution and its symmetric-weight reduction -/

open Finset MetaMathlibExt

-- At `p = -2` and `n = 3`, the summands are `50`, `120`, `180`, and `0`.
-- Compute the sum and the closed form independently.
example :
    (∑ k ∈ range (3 + 1),
        ((2 * 3 : ℕ).choose (2 * k) * catalan k * catalan (3 - k) : ℤ) *
          lucasU ⟨-2, -1, by decide⟩ (3 - k) * lucasV ⟨-2, -1, by decide⟩ k) = 350 ∧
      (catalan 3 * catalan 4 : ℤ) * lucasU ⟨-2, -1, by decide⟩ 3 = 350 := by
  constructor <;>
    norm_num [sum_range_succ, catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose] <;> decide

-- At `p = 0` and `n = 0`, the single term and the closed form both vanish.
example :
    (∑ k ∈ range (0 + 1),
        ((2 * 0 : ℕ).choose (2 * k) * catalan k * catalan (0 - k) : ℤ) *
          lucasU ⟨0, -1, by decide⟩ (0 - k) * lucasV ⟨0, -1, by decide⟩ k) = 0 ∧
      (catalan 0 * catalan 1 : ℤ) * lucasU ⟨0, -1, by decide⟩ 0 = 0 := by
  constructor <;> decide

-- The public theorem also evaluates the sum for Pell parameters.
example :
    ∑ k ∈ range (2 + 1),
        ((2 * 2 : ℕ).choose (2 * k) * catalan k * catalan (2 - k) : ℤ) *
          lucasU ⟨2, -1, by decide⟩ (2 - k) * lucasV ⟨2, -1, by decide⟩ k = 20 := by
  rw [lucasU_lucasV_sum_choose_catalan]
  norm_num [catalan_two, catalan_three]
  decide

private def weights (k : ℕ) : ℤ := if k = 1 then -5 else 2

-- Test the symmetric-weight identity directly with nonconstant signed weights and `Q = 2`.
example :
    (∀ k ≤ 2, weights (2 - k) = weights k) ∧
      (∑ k ∈ range (2 + 1), weights k * lucasU ⟨3, 2, by decide⟩ (2 - k) *
        lucasV ⟨3, 2, by decide⟩ k) = -3 ∧
      (∑ k ∈ range (2 + 1), weights k) * lucasU ⟨3, 2, by decide⟩ 2 = -3 := by
  refine ⟨?_, by decide, by decide⟩
  intro k hk
  have h : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide
