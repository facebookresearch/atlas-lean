/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PadovanPerrinFundamentalProduct
import Mathlib.Tactic.NormNum

open MetaMathlibExt

private abbrev v := padovanPerrinFundamental (2 : ℤ) 3 1 2

private theorem v_initial (j n : ℕ) (hn : n < 3) : v j n = if n + 1 = j then 1 else 0 :=
  padovanPerrinFundamental_of_lt 2 3 1 2 j n hn

private theorem v_step (j n : ℕ) : v j (n + 3) = 2 * v j (n + 1) + 3 * v j n :=
  (padovanPerrinRecurrence_isSolution_iff 2 3 1 2 (by decide) (v j)).mp
    (padovanPerrinFundamental_isSolution 2 3 1 2 j) n

private theorem v_three (j : ℕ) : v j 3 = 2 * v j 1 + 3 * v j 0 := v_step j 0

private theorem v_four (j : ℕ) : v j 4 = 2 * v j 2 + 3 * v j 1 := v_step j 1

private theorem interval : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide

-- `m = 0` at the first row and column, and `n = 0` at the last row.
example : v 3 4 = ∑ k ∈ Finset.Icc 1 3, v (3 - k + 1) 2 * v 3 (2 + 3 - k) := by
  exact padovanPerrinFundamental_mul_sum (k₁ := (2 : ℤ)) (k₂ := 3) (p := 1) (s := 2)
    (hp := by decide) (hs := by decide) (m := 0) (n := 2) (i := 1) (j := 1)
    (hi := by decide) (hi' := by decide) (hj := by decide) (hj' := by decide)

example : v 2 4 = ∑ k ∈ Finset.Icc 1 3, v (3 - k + 1) 4 * v 2 (3 - k) := by
  exact padovanPerrinFundamental_mul_sum (2 : ℤ) 3 1 2 (by decide) (by decide)
    4 0 3 2 (by decide) (by decide) (by decide) (by decide)

-- With `m = 2`, `n = 1`, `i = 1`, `j = 3`, the product entry is nonzero.
example : (∑ k ∈ Finset.Icc 1 3, v (3 - k + 1) 4 * v 1 (4 - k)) = 6 := by
  rw [← padovanPerrinFundamental_mul_sum (2 : ℤ) 3 1 2 (by decide) (by decide)
    2 1 1 3 (by decide) (by decide) (by decide) (by decide)]
  change v 1 5 = 6
  rw [show v 1 5 = 2 * v 1 3 + 3 * v 1 2 from v_step 1 2]
  norm_num [v_three, v_initial]

-- Transposing the outer indices changes the answer.
example : (∑ k ∈ Finset.Icc 1 3, v (3 - k + 1) 2 * v 3 (4 - k)) = 0 := by
  rw [interval]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [v_three, v_initial]

-- Reversing just one occurrence of the inner index changes it as well.
example : (∑ k ∈ Finset.Icc 1 3, v (3 - k + 1) 4 * v 1 k) = 0 := by
  rw [interval]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  norm_num [v_three, v_four, v_initial]
