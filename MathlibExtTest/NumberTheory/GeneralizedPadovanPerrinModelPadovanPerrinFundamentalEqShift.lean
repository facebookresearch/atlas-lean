/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModelPadovanPerrinFundamentalEqShift
import Mathlib.Tactic.NormNum
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.Polynomial.Roots
import MathlibExt.NumberTheory.GeneralizedPadovanPerrinExpansion
import MathlibExt.NumberTheory.GeneralizedPadovanPerrinModel
import MathlibExt.NumberTheory.PadovanPerrinFundamentalProduct

/-! # Tests for the shift property of the Padovan–Perrin fundamental system -/

namespace MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelPadovanPerrinFundamentalEqShift

open MetaMathlibExt

private abbrev v := padovanPerrinFundamental (2 : ℤ) 3 1 4

private theorem v_initial (j n : ℕ) (hn : n < 5) : v j n = if n + 1 = j then 1 else 0 :=
  padovanPerrinFundamental_of_lt 2 3 1 4 j n hn

private theorem v_step (j n : ℕ) : v j (n + 5) = 2 * v j (n + 1) + 3 * v j n := by
  have h := (padovanPerrinRecurrence_isSolution_iff (2 : ℤ) 3 1 4 (by decide) (v j)).mp
    (padovanPerrinFundamental_isSolution 2 3 1 4 j) n
  simpa using h

-- With `p = 1`, `s = 4`, `j = 3` lies strictly inside `[p+1, s+p-1] = [2, 4]`, and `n = 6`
-- gives the nonzero value `k₁ = 2` on both sides of the shift.
example : v 3 6 = 2 := by
  have h := (padovanPerrinFundamental_eq_shift (2 : ℤ) 3 1 4 3 (by decide) (by decide)
    (by decide)).1 6
  change v 3 6 = v 5 (6 + (4 + 1) - 3) at h
  have h8 : 6 + (4 + 1) - 3 = 8 := by decide
  rw [h8] at h
  rw [h]
  have hs : v 5 8 = 2 * v 5 4 + 3 * v 5 3 := by
    have := v_step 5 3
    simpa using this
  rw [hs]
  norm_num [v_initial]

-- The same value through the one-step unfolding for `n ≥ j`.
example : v 3 6 = 2 := by
  have h : v 3 6 = 2 * v 5 4 + 3 * v 5 3 :=
    (padovanPerrinFundamental_eq_shift (2 : ℤ) 3 1 4 3 (by decide) (by decide)
      (by decide)).2 6 (by decide)
  rw [h]
  norm_num [v_initial]

end MathlibExtTest.NumberTheory.GeneralizedPadovanPerrinModelPadovanPerrinFundamentalEqShift
