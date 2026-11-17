/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.AverageOmegaHFree

/-!
# Tests for the newly public lemmas of the `h`-free average-order development
-/

@[expose] public section

open Finset

-- `h = 2`, `y = 0`: no integers are counted and the bound is `|0 - 0| ≤ 0`.
example : |((((Icc 1 ⌊(0 : ℝ)⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, n.factorization p < 2)).card : ℕ) : ℝ)
    - 0 / (riemannZeta ((2 : ℕ) : ℂ)).re| ≤ 4 * Real.sqrt 0 :=
  MetaMathlibExt.abs_card_hfree_sub_le 2 le_rfl 0 le_rfl

-- The `h`-free count at `y = 10`, `h = 2` (squarefree numbers): `1, 2, 3, 5, 6, 7, 10`.
example : ((Icc 1 10).filter (fun n => ∀ p ∈ n.primeFactors, n.factorization p < 2)).card = 7 := by
  decide +kernel
