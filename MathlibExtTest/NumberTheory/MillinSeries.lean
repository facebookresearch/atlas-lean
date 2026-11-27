/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MillinSeries

open MetaMathlibExt

-- With zero-based indexing the first three denominators are F₂, F₄ and F₈.
example {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) ((5 - √5) / 2)) :
    a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 21 := by
  have h := eq_fib_two_pow_of_ratio_le_of_hasSum_millin hpos hratio hsum
  exact ⟨h 0, h 1, h 2⟩
