/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDNodeOddSuccessor

/-! # Tests for the D-node successor formula at odd arguments -/

open MetaMathlibExt

-- The smallest odd argument gives no change in the count.
example : (dcDNodes 2 : ℤ) = dcDNodes 1 := by
  have h := dcDNodes_succ_of_odd 1 ⟨0, rfl⟩
  rw [show 1 + 1 = 2 by decide, show Nat.log 2 1 = 0 by decide,
    show (Nat.digits 2 1).sum = 1 by decide] at h
  omega

-- The count drops by two when the successor is a power of two.
example : (dcDNodes 8 : ℤ) - dcDNodes 7 = -2 := by
  have h := dcDNodes_succ_of_odd 7 ⟨3, rfl⟩
  rw [show 7 + 1 = 8 by decide, show Nat.log 2 7 = 2 by decide,
    show (Nat.digits 2 7).sum = 3 by decide] at h
  omega
