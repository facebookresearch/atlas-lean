/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Ring.Basic

/-!
# A square–triangular number identity

For `n ≥ 2`, the increase from the square of `n - 1` to the square of `n` equals
the increase between the triangular numbers at indices `n - 2` and `n`.
-/

namespace MetaMathlibExt

/-- **A square–triangular number identity.** Let $t_v = v(v + 1)/2$ denote the $v$-th triangular
number. For every natural number $n \ge 2$, $n^2 + t_{n-2} = (n - 1)^2 + t_n$.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 1 (`integers-2026-A103-lem-1`). -/
public theorem sq_add_triangular_sub_two_eq (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 + (n - 2) * (n - 2 + 1) / 2 = (n - 1) ^ 2 + n * (n + 1) / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  change (k + 2) ^ 2 + k * (k + 1) / 2 = (k + 1) ^ 2 + (k + 2) * (k + 3) / 2
  simp only [← Nat.mul_add_div (by decide : 0 < 2)]
  exact congrArg (· / 2) (by ring1)

end MetaMathlibExt
