/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Logic.Function.Iterate

/-!
# Comparison of iterated factorials

`Nat.factorial^[j] m` is the `j`-fold iterated factorial `m!⋯!` of a natural number `m`. The
factorial is strictly increasing on the positive integers and maps them to positive integers, so
every iterate `Nat.factorial^[j]` is strictly increasing on the positive integers. Splitting
`Nat.factorial^[k] n = Nat.factorial^[k'] (Nat.factorial^[k - k'] n)` for `k' ≤ k` then compares
iterated factorials of different depths.

## Main results

* `MetaMathlibExt.iterate_factorial_lt_iterate_factorial`: if `n, n' ≥ 3`, `k' < k` and
  `n' < Nat.factorial^[k - k'] n`, then `Nat.factorial^[k'] n' < Nat.factorial^[k] n`.
-/

namespace MetaMathlibExt

/-- Every iterate of the factorial is strictly increasing on the positive integers. -/
private theorem iterate_factorial_lt_of_lt (j : ℕ) {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Nat.factorial^[j] a < Nat.factorial^[j] b := by
  induction j generalizing a b with
  | zero => exact hab
  | succ j ih => exact ih (Nat.factorial_pos a) ((Nat.factorial_lt ha).2 hab)

-- The hypothesis `3 ≤ n` is kept to match the stated theorem; the proof does not use it.
set_option linter.unusedVariables false in
/-- **Comparison of iterated factorials.** For natural numbers $j$ and $m$ let $F_j(m)$ be the
$j$-fold iterated factorial $m!\cdots!$ (with $j$ factorials). Let $n, n' \ge 3$ and $k > k'$ be
natural numbers. If $n' < F_{k-k'}(n)$, then $F_{k'}(n') < F_k(n)$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of Integer
Sequences 28 (2025), Article 25.2.8, Theorem 4 (`jis-2025-25.2.8-thm-4`). -/
public theorem iterate_factorial_lt_iterate_factorial {n n' k k' : ℕ} (hn : 3 ≤ n)
    (hn' : 3 ≤ n') (hk : k' < k) (h : n' < Nat.factorial^[k - k'] n) :
    Nat.factorial^[k'] n' < Nat.factorial^[k] n := by
  rw [← Nat.add_sub_cancel' (Nat.le_of_lt hk), Function.iterate_add_apply]
  exact iterate_factorial_lt_of_lt k' (by omega) h

end MetaMathlibExt
