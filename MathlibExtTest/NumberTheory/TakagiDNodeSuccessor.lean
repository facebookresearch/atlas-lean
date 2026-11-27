/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TakagiDNodeSuccessor

/-! # Tests for the divide-and-conquer D-node successor formula -/

open MetaMathlibExt

-- The smallest positive argument has no change in the count.
example : (dcDNodes 2 : ℤ) = dcDNodes 1 := by
  have h := dcDNodes_succ 1 (by decide)
  rw [show 1 + 1 = 2 by decide, show (Nat.digits 2 1).sum = 1 by decide,
    show Nat.log 2 1 = 0 by decide] at h
  omega

-- The count drops by two into a power of two, then rises by three.
example : (dcDNodes 8 : ℤ) - dcDNodes 7 = -2 := by
  have h := dcDNodes_succ 7 (by decide)
  rw [show 7 + 1 = 8 by decide, show (Nat.digits 2 7).sum = 3 by decide,
    show Nat.log 2 7 = 2 by decide] at h
  omega

example : (dcDNodes 9 : ℤ) - dcDNodes 8 = 3 := by
  have h := dcDNodes_succ 8 (by decide)
  rw [show 8 + 1 = 9 by decide, show (Nat.digits 2 8).sum = 1 by decide,
    show Nat.log 2 8 = 3 by decide] at h
  omega
