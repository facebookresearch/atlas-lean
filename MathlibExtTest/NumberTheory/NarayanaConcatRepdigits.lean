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
