/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NarayanaConcatRepdigits

/-! # Tests for repdigit concatenations -/

open MetaMathlibExt

-- The first digit must be positive and strictly below the base.
example (n : ℕ) : ¬ IsConcatTwoRepdigitsBase 1 n := by
  rintro ⟨a, _, _, _, ha, ha', _⟩
  exact (ha.trans_lt ha').false

-- The first admissible term, 2 = (10)₂, attains the lower digit-count bound.
example {α : ℝ} (hα : α ^ 3 = α ^ 2 + 1) :
    Real.log 2 + Real.log α < 4 * Real.log α ∧ 4 * Real.log α < 2 * Real.log 2 + 1 := by
  have h := narayanaCowsSequence_concat_log_bounds hα
    (n := 4) (b := 2) (a₁ := 1) (a₂ := 0) (l := 1) (m := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  norm_num at h ⊢
  exact h
