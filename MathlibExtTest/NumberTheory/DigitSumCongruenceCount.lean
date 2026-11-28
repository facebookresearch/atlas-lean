/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DigitSumCongruenceCount

open MetaMathlibExt

-- Integer representatives on opposite sides of the final partial block.
example : Nat.count (fun x : ℕ => (x : ℤ) ≡ -3 [ZMOD 4]) 6 = 2 ∧
    Nat.count (fun x : ℕ => (x : ℤ) ≡ -1 [ZMOD 4]) 6 = 1 := by
  decide +kernel

example : Nat.count (fun x : ℕ => (x : ℤ) ≡ -3 [ZMOD 4]) 6 = 2 :=
  (Nat.count_intModEq_card (q := 4) (by decide) (-3) 6).trans (by decide +kernel)

-- An empty tail and a negative representative of the zero class.
example :
    digitSumCongruenceCount 5 1 4 (-4) 0 6 = 2 ∧
      digitSumCongruenceCount 5 1 4 (-4) 1 6 = 1 := by decide

-- At base one every tail digit is zero, but the leading coordinate is unrestricted.
example : digitSumCongruenceCount 1 3 4 (-1) 0 6 = 1 := by decide

-- Modulus one counts every tuple; the interval [1, 1) still contributes nothing.
example :
    digitSumCongruenceCount 2 3 1 (-1) 0 3 = 12 ∧
      digitSumCongruenceCount 2 3 1 (-1) 1 1 = 0 := by decide

-- The interval [0, 6) contains a complete block and a partial block with residue 1.
example : (digitSumCongruenceCount 5 2 4 (-3) 0 6 : ℚ) = 8 := by
  have h := (digitSumCongruenceCount_of_modEq_one (a := 6) (b := 5) (k := 2) (q := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (-3)).2.2.1
  exact h.trans (by decide +kernel)
