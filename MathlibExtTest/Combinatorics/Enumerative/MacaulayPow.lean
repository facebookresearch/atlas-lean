/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MacaulayPow

@[expose] public section

-- Below the first full binomial block the function is the identity.
example : Nat.macaulayPow 2 1 = 1 := Nat.macaulayPow_succ_of_le 1 1 (by decide)

-- At level one it is `C(a + 1, 2)`.
example : Nat.macaulayPow 1 3 = 6 := by rw [Nat.macaulayPow_one]; decide

-- `4 = C(3, 2) + C(1, 1)`, so `4^⟨2⟩ = C(4, 3) + C(2, 2) = 5`.
example : Nat.macaulayPow 2 4 = 5 := by
  rw [Nat.macaulayPow_succ_eq 1 4 3 (by decide) (by decide), Nat.macaulayPow_one]; decide

example (d : ℕ) {a b : ℕ} (h : a ≤ b) : Nat.macaulayPow d a ≤ Nat.macaulayPow d b :=
  Nat.macaulayPow_mono d h

-- Consumer of the cascade form with the original binders.
example (d : ℕ) (a : Fin d → ℕ) (ha : StrictMono a) :
    Nat.macaulayPow d (∑ i, (a i).choose (i.val + 1)) = ∑ i, (a i + 1).choose (i.val + 2) :=
  Nat.macaulayPow_sum_choose d a ha

-- On the strict cascade `a = ![1, 3]`, `C(1, 1) + C(3, 2) = 4` and the value is
-- `C(2, 2) + C(4, 3) = 5`, matching the greedy recursion above.
example : Nat.macaulayPow 2 4 = 5 := by
  convert Nat.macaulayPow_sum_choose 2 ![1, 3] (Fin.strictMono_iff_lt_succ.2 (by decide))
    using 2 <;> decide
