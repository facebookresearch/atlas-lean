/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.CommaParent

open MetaMathlibExt

-- At the smallest base and the square threshold, the parent is 1.
example : IsCommaCandidate 2 1 1 := by
  obtain ⟨k, hk, y, hy, h⟩ := exists_commaParent_of_sq_le 2 4 (by decide) (by decide)
  have hd := hy.2
  rw [← h] at hd
  change 1 = y.val at hd
  have hk' : k = 1 := by omega
  have hy' : y = 1 := Fin.ext hd.symm
  simpa only [hk', hy'] using hy

-- The decimal parent of 200 also has a smaller child, 199.
example : IsCommaCandidate 10 118 1 ∧ IsCommaCandidate 10 118 2 ∧
    199 = 118 + 10 * (118 % 10) + 1 ∧ 200 = 118 + 10 * (118 % 10) + 2 := by
  unfold IsCommaCandidate commaMsd
  decide
