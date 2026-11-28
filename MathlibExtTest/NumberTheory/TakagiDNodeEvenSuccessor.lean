/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDNodeEvenSuccessor

/-! # Tests for the D-node successor formula at even arguments -/

open MetaMathlibExt

-- At the smallest positive even argument, the count rises by one.
example : (dcDNodes 3 : ℤ) - dcDNodes 2 = 1 := by
  have h := dcDNodes_succ_of_even 2 (by decide) ⟨1, rfl⟩
  rw [show 2 + 1 = 3 by decide, show Nat.log 2 2 = 1 by decide,
    show (Nat.digits 2 2).sum = 1 by decide] at h
  omega

-- An even argument with three ones can give a negative change in the count.
example : (dcDNodes 15 : ℤ) - dcDNodes 14 = -1 := by
  have h := dcDNodes_succ_of_even 14 (by decide) ⟨7, rfl⟩
  rw [show 14 + 1 = 15 by decide, show Nat.log 2 14 = 3 by decide,
    show (Nat.digits 2 14).sum = 3 by decide] at h
  omega
