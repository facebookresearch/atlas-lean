/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Partial-sum identities for the Hopkins–Wang tribonacci numbers

Let `t(0) = 1`, `t(1) = 0`, `t(2) = 1` and `t(n) = t(n-1) + t(n-2) + t(n-3)` for `n ≥ 3`, and
set `t(n) = 0` for `n < 0`; on the naturals this is `tribNat`, on the integers `trib`.
The theorem `trib_three_mul` expresses `t(3k)` as one plus the sum of the two
preceding terms at each multiple of three from `0` through `3k`. The theorems
`trib_add_two_sub_three_mul` and `trib_add_two_sub_three_mul_add_two` express `t(n) + t(n-2)` as
`2 ∑_{i=0}^{k-1} t(n-3i-1)` for `n = 3k, 3k + 1`, and as `2 + 2 ∑_{i=0}^{k-1} t(n-3i-1)` for
`n = 3k + 2`, respectively, with `k ≥ 1` in each case.

## Proof outline for `trib_add_two_sub_three_mul_add_two`

All indices are nonnegative, so the identity is one about `tribNat`, where the sum reads
`s(k) = t(3k+1) + t(3k-2) + ⋯ + t(4)`. Induct on `k`. For `k = 1` both sides equal
`t(5) + t(3) = 6 + 2 = 2 + 2 t(4)`. Passing from `k` to `k + 1` adds `2 t(3k+4)` to the right
side, and adds `t(3k+5) + t(3k+3) - t(3k+2) - t(3k)` to the left side. Expanding `t(3k+5)` and
then `t(3k+3)` by the recurrence turns the latter into
`t(3k+4) + t(3k+3) + t(3k+2) + t(3k+1) = 2 t(3k+4)`. The identity also holds for `k = 0`, where
it reads `t(2) + t(0) = 2`, but the statement keeps the hypothesis `k ≥ 1`.

## Implementation notes

`tribNat`, `trib` and `trib_add_two_sub_three_mul_add_two` keep the full names, bodies,
statements and docstrings they had in
`WantedExt.Combinatorics.Enumerative.NColorCompositionsWanted`, so their namespace reads
`NColorCompositionsWanted`. That module imports this one and keeps its other wanted statements
about these numbers and about restricted `n`-color compositions; the docstring of
`trib_add_two_sub_three_mul_add_two` cites the source of the statement.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

/-- **Tribonacci numbers with initial values $1, 0, 1$.** The sequence
$t : \mathbb{N} \to \mathbb{Z}$ with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$. -/
def tribNat : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | n + 3 => tribNat (n + 2) + tribNat (n + 1) + tribNat n

/-- **Hopkins–Wang tribonacci numbers on the integers.** Let $t(0) = 1$, $t(1) = 0$,
$t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for natural numbers $n \ge 3$. This
extends $t$ to an integer-valued function on all integers by setting $t(n) = 0$ for
$n < 0$. -/
def trib (n : ℤ) : ℤ :=
  if 0 ≤ n then tribNat n.toNat else 0

/-- At an integer equal to a natural number `m`, `trib` takes the value `tribNat m`. -/
private theorem trib_eq_tribNat {n : ℤ} {m : ℕ} (h : n = m) : trib n = tribNat m := by
  simp [trib, h]

/-- The recurrence of `tribNat`. -/
private theorem tribNat_add_three (n : ℕ) :
    tribNat (n + 3) = tribNat (n + 2) + tribNat (n + 1) + tribNat n :=
  rfl

/-- The recurrence on integer indices at least three. -/
private theorem trib_recurrence (n : ℤ) (hn : 3 ≤ n) :
    trib n = trib (n - 1) + trib (n - 2) + trib (n - 3) := by
  let j := (n - 3).toNat
  rw [trib_eq_tribNat (m := j + 3) (by omega), trib_eq_tribNat (m := j + 2) (by omega),
    trib_eq_tribNat (m := j + 1) (by omega), trib_eq_tribNat (m := j) (by omega)]
  exact tribNat_add_three j

/-- The identity for `tribNat`, with the sum indexed as `t(3(k - i) + 1)` for `i < k`. -/
private theorem tribNat_add_two_sub_three_mul_add_two (k : ℕ) (hk : 1 ≤ k) :
    tribNat (3 * k + 2) + tribNat (3 * k) =
      2 + 2 * ∑ i ∈ Finset.range k, tribNat (3 * (k - i) + 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    have h3 : tribNat (3 * k + 3) =
        tribNat (3 * k + 2) + tribNat (3 * k + 1) + tribNat (3 * k) := tribNat_add_three _
    have h4 : tribNat (3 * k + 4) =
        tribNat (3 * k + 3) + tribNat (3 * k + 2) + tribNat (3 * k + 1) := tribNat_add_three _
    have h5 : tribNat (3 * k + 5) =
        tribNat (3 * k + 4) + tribNat (3 * k + 3) + tribNat (3 * k + 2) := tribNat_add_three _
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [show 3 * (k + 1) + 2 = 3 * k + 5 by omega, show 3 * (k + 1) + 1 = 3 * k + 4 by omega,
      show 3 * (k + 1) = 3 * k + 3 by omega]
    linear_combination h5 - h4 + h3 + ih

/-- **Identity for $t(n) + t(n-2)$ when $n \ge 3$ and $n \equiv 2 \pmod 3$.** Let $t$ be the
tribonacci numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every
natural number $k \ge 1$, with $n = 3k + 2$,
$$t(n) + t(n-2) = 2 + 2 \sum_{i=0}^{k-1} t(n-3i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem trib_add_two_sub_three_mul_add_two (k : ℕ)
    (hk : 1 ≤ k) :
    trib (3 * (k : ℤ) + 2) + trib (3 * (k : ℤ) + 2 - 2) =
      2 + 2 * ∑ i ∈ Finset.range k,
        trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) := by
  have hsum : ∑ i ∈ Finset.range k, trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) =
      ∑ i ∈ Finset.range k, tribNat (3 * (k - i) + 1) :=
    Finset.sum_congr rfl fun i hi =>
      trib_eq_tribNat (by have := Finset.mem_range.mp hi; omega)
  rw [trib_eq_tribNat (m := 3 * k + 2) (by omega), trib_eq_tribNat (m := 3 * k) (by omega), hsum]
  exact tribNat_add_two_sub_three_mul_add_two k hk

/-- **Tribonacci partial-sum identity for $t(3k)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k) = 1 + \sum_{i=0}^{k} \bigl(t(3k-3i-1) + t(3k-3i-2)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem trib_three_mul (k : ℕ) :
    trib (3 * (k : ℤ)) = 1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 2)) := by
  induction k with
  | zero =>
    -- The only summand is `t(-1) + t(-2) = 0`.
    decide
  | succ k ih =>
    -- Removing the first summand leaves the indices for `k`.
    have hshift (i : ℕ) :
        3 * ((k + 1 : ℕ) : ℤ) - 3 * ((i + 1 : ℕ) : ℤ) =
          3 * (k : ℤ) - 3 * (i : ℤ) := by
      omega
    have hrec : trib (3 * ((k + 1 : ℕ) : ℤ)) =
        trib (3 * ((k + 1 : ℕ) : ℤ) - 1) +
          trib (3 * ((k + 1 : ℕ) : ℤ) - 2) + trib (3 * (k : ℤ)) := by
      rw [trib_eq_tribNat (m := 3 * k + 3) (by omega),
        trib_eq_tribNat (m := 3 * k + 2) (by omega),
        trib_eq_tribNat (m := 3 * k + 1) (by omega),
        trib_eq_tribNat (m := 3 * k) (by omega)]
      exact tribNat_add_three _
    rw [Finset.sum_range_succ']
    simp only [hshift, Nat.cast_zero, mul_zero, sub_zero]
    rw [hrec, ih]
    ac_rfl

/-- **Tribonacci partial-sum identity for $t(3k+1)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k+1) = -1 + \sum_{i=0}^{k} \bigl(t(3k-3i) + t(3k-3i-1)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem trib_three_mul_add_one (k : ℕ) :
    trib (3 * (k : ℤ) + 1) = -1 +
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 2)) := by
  -- An elementary recurrence proof: the first summand accounts for the step of length three.
  induction k with
  | zero =>
    -- The only summand is `t(0) + t(-1) = 1`, which cancels the `-1`.
    decide
  | succ k ih =>
    have hshift (i : ℕ) :
        3 * ((k + 1 : ℕ) : ℤ) + 1 - 3 * ((i + 1 : ℕ) : ℤ) =
          3 * (k : ℤ) + 1 - 3 * (i : ℤ) := by omega
    rw [Finset.sum_range_succ']
    simp only [hshift, Nat.cast_zero, mul_zero, sub_zero]
    rw [trib_recurrence _ (by omega),
      show 3 * ((k + 1 : ℕ) : ℤ) + 1 - 3 = 3 * (k : ℤ) + 1 by omega, ih]
    ac_rfl

/-- One step of length three for the sum `t(n) + t(n-2)`. -/
private theorem trib_add_two_sub_step (n : ℤ) (hn : 5 ≤ n) :
    trib n + trib (n - 2) = 2 * trib (n - 1) + (trib (n - 3) + trib (n - 5)) := by
  have h0 := trib_recurrence n (by omega)
  have h1 := trib_recurrence (n - 1) (by omega)
  have h2 := trib_recurrence (n - 2) (by omega)
  rw [show n - 1 - 1 = n - 2 by omega, show n - 1 - 2 = n - 3 by omega,
    show n - 1 - 3 = n - 4 by omega] at h1
  rw [show n - 2 - 1 = n - 3 by omega, show n - 2 - 2 = n - 4 by omega,
    show n - 2 - 3 = n - 5 by omega] at h2
  linear_combination h0 - h1 + h2

/-- **Identity for $t(n) + t(n-2)$ when $n \ge 3$ and $n \equiv 0, 1 \pmod 3$.** Let $t$ be the
tribonacci numbers with $t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and
$t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$, extended by $t(n) = 0$ for $n < 0$. For every
natural number $k \ge 1$, both $n = 3k$ and $n = 3k + 1$ satisfy
$$t(n) + t(n-2) = 2 \sum_{i=0}^{k-1} t(n-3i-1).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 9. -/
theorem trib_add_two_sub_three_mul (k : ℕ) (hk : 1 ≤ k) :
    trib (3 * (k : ℤ)) + trib (3 * (k : ℤ) - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) - 3 * (i : ℤ) - 1) ∧
      trib (3 * (k : ℤ) + 1) + trib (3 * (k : ℤ) + 1 - 2) =
        2 * ∑ i ∈ Finset.range k,
          trib (3 * (k : ℤ) + 1 - 3 * (i : ℤ) - 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hstep (n : ℤ) (hn : 2 ≤ n)
        (h : trib n + trib (n - 2) =
          2 * ∑ i ∈ Finset.range k, trib (n - 3 * (i : ℤ) - 1)) :
        trib (n + 3) + trib (n + 3 - 2) =
          2 * ∑ i ∈ Finset.range (k + 1), trib (n + 3 - 3 * (i : ℤ) - 1) := by
      -- Removing the first summand leaves the indices for `n`.
      have hshift (i : ℕ) :
          n + 3 - 3 * ((i + 1 : ℕ) : ℤ) = n - 3 * (i : ℤ) := by omega
      rw [Finset.sum_range_succ']
      simp only [hshift, Nat.cast_zero, mul_zero, sub_zero]
      rw [trib_add_two_sub_step (n + 3) (by omega),
        show n + 3 - 3 = n by omega, show n + 3 - 5 = n - 2 by omega, h, mul_add]
      ac_rfl
    constructor
    · rw [show 3 * ((k + 1 : ℕ) : ℤ) = 3 * (k : ℤ) + 3 by omega]
      exact hstep _ (by omega) ih.1
    · rw [show 3 * ((k + 1 : ℕ) : ℤ) + 1 = (3 * (k : ℤ) + 1) + 3 by omega]
      exact hstep _ (by omega) ih.2

/-- **Tribonacci partial-sum identity for $t(3k+2)$.** Let $t$ be the tribonacci numbers with
$t(0) = 1$, $t(1) = 0$, $t(2) = 1$ and $t(n) = t(n-1) + t(n-2) + t(n-3)$ for $n \ge 3$,
extended by $t(n) = 0$ for $n < 0$. For every natural number $k$,
$$t(3k+2) = \sum_{i=0}^{k} \bigl(t(3k-3i+1) + t(3k-3i)\bigr).$$

Source: Brian Hopkins and Hua Wang, "Allowing or Prohibiting
Two Consecutive Colors in `n`-Color Compositions",
Theorem 8. -/
theorem trib_three_mul_add_two (k : ℕ) :
    trib (3 * (k : ℤ) + 2) =
      ∑ i ∈ Finset.range (k + 1),
        (trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 1) +
          trib (3 * (k : ℤ) + 2 - 3 * (i : ℤ) - 2)) := by
  let term (j i : ℕ) :=
    trib (3 * (j : ℤ) + 2 - 3 * (i : ℤ) - 1) +
      trib (3 * (j : ℤ) + 2 - 3 * (i : ℤ) - 2)
  change trib (3 * (k : ℤ) + 2) = ∑ i ∈ Finset.range (k + 1), term k i
  induction k with
  | zero => norm_num [term, trib, tribNat, Finset.sum_range_one]
  | succ k ih =>
    have hrec : trib (3 * ((k + 1 : ℕ) : ℤ) + 2) =
        trib (3 * ((k + 1 : ℕ) : ℤ) + 2 - 1) +
          trib (3 * ((k + 1 : ℕ) : ℤ) + 2 - 2) + trib (3 * (k : ℤ) + 2) := by
      let j := 3 * k + 2
      rw [trib_eq_tribNat (m := j + 3) (by dsimp [j]; omega),
        trib_eq_tribNat (m := j + 2) (by dsimp [j]; omega),
        trib_eq_tribNat (m := j + 1) (by dsimp [j]; omega),
        trib_eq_tribNat (m := j) (by dsimp [j])]
      exact tribNat_add_three j
    have htail (i : ℕ) : term (k + 1) (i + 1) = term k i := by
      dsimp [term]
      exact congrArg₂ (· + ·) (congrArg trib (by omega)) (congrArg trib (by omega))
    rw [Finset.sum_range_succ', show (∑ i ∈ Finset.range (k + 1), term (k + 1) (i + 1)) =
      ∑ i ∈ Finset.range (k + 1), term k i from Finset.sum_congr rfl (fun i _ => htail i), ← ih]
    rw [hrec]
    simp only [term, Nat.cast_zero, mul_zero, sub_zero]
    ac_rfl

end MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted
