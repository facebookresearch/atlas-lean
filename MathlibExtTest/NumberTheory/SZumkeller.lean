/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SZumkeller

/-! # Tests for the criterion for even s-Zumkeller numbers -/

open MetaMathlibExt

-- Reinserting 30 into this witness gives the equal-squares part {1, 2, 5, 30}.
example : IsSZumkeller 60 := by
  apply (isSZumkeller_iff_of_even 60 (by decide) (by decide)).2
  exact ⟨{1, 2, 5}, by decide, by decide⟩

-- For the smallest positive even integer the right-hand side is negative.
example : ¬ IsSZumkeller 2 := by
  intro h
  obtain ⟨S, _, hsum⟩ := (isSZumkeller_iff_of_even 2 (by decide) (by decide)).1 h
  have hneg : 4 * (∑ d ∈ S, d ^ 2 : ℤ) < 0 := hsum.trans_lt (by decide)
  exact hneg.not_ge (mul_nonneg (by decide) (Finset.sum_nonneg fun d _ => sq_nonneg (d : ℤ)))
