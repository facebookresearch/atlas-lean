/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BalancingRepdigit

/-! # Tests for the decimal blocks of Lucas-balancing numbers -/

open MetaMathlibExt

-- Both solutions occur with the shifted indexing and the specified block lengths.
example : lucasBalancingNum 3 = 17 ∧ IsConcatTwoRepdigits (lucasBalancingNum 3).toNat :=
  ⟨rfl, 1, 7, 1, 1, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

example : lucasBalancingNum 5 = 577 ∧ IsConcatTwoRepdigits (lucasBalancingNum 5).toNat :=
  ⟨rfl, 5, 7, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

-- The intervening term 99 has just one run.
example : ¬ IsConcatTwoRepdigits 99 := by
  intro h
  exact (by decide : ¬ (lucasBalancingNum 4 = 17 ∨ lucasBalancingNum 4 = 577))
    (lucasBalancingNum_concatTwoRepdigits (k := 4) (h := h))

-- A trailing block of zeros is allowed.
example : IsConcatTwoRepdigits 100 :=
  ⟨1, 0, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩
