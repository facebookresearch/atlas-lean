/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BoundedSubsequenceSumsPositive

open MetaMathlibExt

-- At α = β = 1 and total length three, the upper length is two and just one padding zero is used.
example : (4 : ℤ) ≤
    (boundedSubsequenceSums 1 1 (repetitionSequence ![(2 : ℤ), 5] ![1, 2])).card := by
  have h := (card_boundedSubsequenceSums_ge_of_pos (k := 2) (by decide)
    ![1, 2] (by decide) 3 (by decide) 1 1 (by decide) (by decide)).1 ![2, 5]
      (by rw [Fin.strictMono_iff_lt_succ]; decide) (by decide)
  rwa [show yangChenBound (Fin.cons (3 - 1 - 1) ![1, 2]) (3 - 1) = 4 by decide] at h

-- With β = 0 the full sequence is allowed; the theorem guarantees a sharp example with six sums.
example : ∃ b : Fin 2 → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧
    ((boundedSubsequenceSums 1 0 (repetitionSequence b ![2, 2])).card : ℤ) = 6 := by
  have h := (card_boundedSubsequenceSums_ge_of_pos (k := 2) (by decide)
    ![2, 2] (by decide) 4 (by decide) 1 0 (by decide) (by decide)).2
  rwa [show yangChenBound (Fin.cons (4 - 1 - 0) ![2, 2]) (4 - 0) = 6 by decide] at h

-- The concrete positive sequence 1, 1, 2, 2 attains the bound.
example : boundedSubsequenceSums 1 0 (repetitionSequence ![(1 : ℤ), 2] ![2, 2]) =
    {1, 2, 3, 4, 5, 6} := by
  decide
