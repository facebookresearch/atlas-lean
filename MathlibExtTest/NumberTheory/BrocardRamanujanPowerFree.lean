/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BrocardRamanujanPowerFree

open MetaMathlibExt Nat

-- The squarefree case: finitely many solutions with `x - 1` or `x + 1` squarefree.
example : {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).IsPowerFree 2 ∨ (p.2 + 1).IsPowerFree 2)}.Finite :=
  brocardRamanujan_powerFree_finite 2 le_rfl

-- The solution `4! + 1 = 5 ^ 2` lies in the set for `k = 7`, since `x + 1 = 6` is `7`-free.
example : ((4, 5) : ℕ × ℕ) ∈ {p : ℕ × ℕ | p.1 ! + 1 = p.2 ^ 2 ∧
    ((p.2 - 1).IsPowerFree 7 ∨ (p.2 + 1).IsPowerFree 7)} := by
  refine ⟨by decide, Or.inr ⟨by norm_num, by norm_num, fun p hp hdvd => ?_⟩⟩
  have h2 : 2 ≤ p := hp.two_le
  have h7 : 2 ^ 7 ≤ p ^ 7 := Nat.pow_le_pow_left h2 7
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

-- At `(4, 5)` it is the lower neighbour, `4`, that satisfies the prime-power condition.
example : ((4, 5) : ℕ × ℕ) ∈ ({(4, 5)} : Set (ℕ × ℕ)) :=
  brocardRamanujan_primePow_subset (a := (4, 5)) ⟨by decide, Or.inl (by decide)⟩

-- The other two known solutions of the equation fail the prime-power condition.
example : 5 ! + 1 = 11 ^ 2 ∧ ¬ (IsPrimePow (11 - 1 : ℕ) ∨ IsPrimePow (11 + 1 : ℕ)) := by
  decide

example : 7 ! + 1 = 71 ^ 2 ∧ ¬ (IsPrimePow (71 - 1 : ℕ) ∨ IsPrimePow (71 + 1 : ℕ)) := by
  decide
