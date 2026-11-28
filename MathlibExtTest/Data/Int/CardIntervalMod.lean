/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Int.CardIntervalMod

-- Integer representatives on opposite sides of the final partial block.
example : Nat.count (fun x : ℕ => (x : ℤ) ≡ -3 [ZMOD 4]) 6 = 2 ∧
    Nat.count (fun x : ℕ => (x : ℤ) ≡ -1 [ZMOD 4]) 6 = 1 := by
  decide +kernel

example : Nat.count (fun x : ℕ => (x : ℤ) ≡ -3 [ZMOD 4]) 6 = 2 :=
  (Nat.count_intModEq_card (q := 4) (by decide) (-3) 6).trans (by decide +kernel)
