/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.CommaChildParent

open MetaMathlibExt

-- The leading 2 and final 0 of 200 recover a parent ending in 8.
example : ∃! k : ℕ, 0 < k ∧ ∃ y : Fin 10, IsCommaCandidate 10 k y ∧
    200 = k + 10 * (k % 10) + y.val := by
  refine ⟨118, ⟨by decide, 2, ?_, rfl⟩, ?_⟩
  · unfold IsCommaCandidate commaMsd
    decide
  · rintro k ⟨hk, hchild⟩
    exact Int.ofNat_inj.mp ((commaChild_parent_eq 10 200 (by decide)).1 k hk hchild)

-- For 10 the formula gives −81, so there is no positive parent.
example : ¬ ∃ k : ℕ, 0 < k ∧ ∃ y : Fin 10, IsCommaCandidate 10 k y ∧
    10 = k + 10 * (k % 10) + y.val :=
  (commaChild_parent_eq 10 10 (by decide)).2 (by decide)
