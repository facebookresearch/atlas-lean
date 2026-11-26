/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHofstadterOrderHofLEqAddHofCount

/-!
# Tests for the image length `L_k` as a letter count
-/

namespace MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofLEqAddHofCount

open MetaMathlibExt

-- First equality on a concrete instance.
example : hofL 2 5 = 5 + hofCount 2 (· = 2) 5 :=
  (hofL_eq_add_hofCount (by decide : 1 ≤ 2) 5).1

-- Second equality on a concrete instance.
example : hofL 2 5 = 5 + (hofstadterF 2)^[2 - 1] 5 :=
  (hofL_eq_add_hofCount (by decide : 1 ≤ 2) 5).2

-- Concrete value of `L_2(5)` via the first equality and a count computation.
example : hofL 2 5 = 8 := by
  have h := (hofL_eq_add_hofCount (by decide : 1 ≤ 2) 5).1
  have hc : hofCount 2 (· = 2) 5 = 3 := by decide
  omega

-- Corollary for `k = 1`: the zeroth iterate is the identity, so `L_1(n) = 2 * n`.
example (n : ℕ) : hofL 1 n = 2 * n := by
  have h := (hofL_eq_add_hofCount (by decide : 1 ≤ 1) n).2
  simp only [Nat.sub_self, Function.iterate_zero_apply] at h
  omega

end MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofLEqAddHofCount
