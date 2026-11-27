/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Addition formula for squared Fibonacci numbers

Write `F_k` for the Fibonacci number `Nat.fib k`. `fib_add_sq_eq` proves that for `m ≥ 1` and
`n ≥ 2`,

`F_(m+n)² = F_(m+1)² F_n² + F_m² F_(n-1)² + 2 (∑_{i=1}^m F_i²) (∑_{j=1}^(n-1) F_j²)`.

Its case `m = 1`, with `n - 1` in place of `n`, is `two_mul_sum_fib_sq`: for `n ≥ 3`,

`2 ∑_{j=1}^(n-2) F_j² = F_n² - F_(n-1)² - F_(n-2)²` (in `ℤ`).

## Proof outline

Write `n = k + 1`. Squaring Mathlib's addition formula `F_(m+k+1) = F_m F_k + F_(m+1) F_(k+1)`
(`Nat.fib_add`) leaves the cross term `2 F_m F_(m+1) F_k F_(k+1)`, which is the product of the
two sums because `∑_{i=1}^k F_i² = F_k F_(k+1)` (by induction on `k`, from
`F_(k+2) = F_k + F_(k+1)`).

For `two_mul_sum_fib_sq`, `fib_add_sq_eq` with `m = 1` and `n - 1 ≥ 2` in place of `n` reads
`F_n² = F_(n-1)² + F_(n-2)² + 2 ∑_{j=1}^(n-2) F_j²` once `F_1 = F_2 = 1` are substituted; casting
this identity to `ℤ` and rearranging gives the statement.

## Implementation notes

`fib_add_sq_eq` and `two_mul_sum_fib_sq` keep the names, the statements and the source citations
of their former wanted entries in
`WantedExt.Combinatorics.Enumerative.BiPeriodicFibonacciSquaredWanted`, which keeps the other
statements of that source.

The statement of `fib_add_sq_eq` keeps the hypotheses `1 ≤ m` and `2 ≤ n` of the wanted entry.
The proof uses only `2 ≤ n`, to write `n = k + 1`: the identity holds for every `m` and every
`n ≥ 1`. The unused-variables linter is turned off for this one declaration because of the unused
hypothesis `1 ≤ m`.

The hypothesis `3 ≤ n` of `two_mul_sum_fib_sq` only excludes `n = 1`, where truncated subtraction
makes the right-hand side `F_1² - F_0² - F_0² = 1` while the left-hand side is the empty sum `0`.
For `n = 0` and `n = 2` both sides are `0`.

The sum of squares `∑_{i=1}^k F_i² = F_k F_(k+1)` is also `MetaMathlibExt.Nat.sum_Icc_fib_sq` in
`MathlibExt.Analysis.MonotonePowerSumInequalities`. It is proved again here, as a private lemma,
so that this file does not import that module's real analysis.
-/

@[expose] public section

namespace MetaMathlibExt

open Finset

namespace fib_add_sq_eq

/-- The sum of the squares of the first `k` Fibonacci numbers: `∑_{i=1}^k F_i² = F_k F_(k+1)`. -/
private theorem sum_Icc_fib_sq_eq_fib_mul_fib_succ (k : ℕ) :
    ∑ i ∈ Icc 1 k, Nat.fib i ^ 2 = Nat.fib k * Nat.fib (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.fib_add_two]
    ring

end fib_add_sq_eq

open fib_add_sq_eq in
set_option linter.unusedVariables false in
/-- **Addition formula for squared Fibonacci numbers.** Let $F_k$ denote the Fibonacci numbers
($F_0 = 0$, $F_1 = 1$). For all natural numbers $m \ge 1$ and $n \ge 2$,
$$
F_{m+n}^2 = F_{m+1}^2 F_n^2 + F_m^2 F_{n-1}^2 +
2 \left(\sum_{i=1}^{m} F_i^2\right) \left(\sum_{j=1}^{n-1} F_j^2\right).
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.12 (`fq-2024-belaggoun01132024-cor-3.12`). -/
theorem fib_add_sq_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    Nat.fib (m + n) ^ 2 =
      Nat.fib (m + 1) ^ 2 * Nat.fib n ^ 2 + Nat.fib m ^ 2 * Nat.fib (n - 1) ^ 2 +
        2 * (∑ i ∈ Icc 1 m, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 (n - 1), Nat.fib j ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, sum_Icc_fib_sq_eq_fib_mul_fib_succ,
    sum_Icc_fib_sq_eq_fib_mul_fib_succ, ← add_assoc, Nat.fib_add]
  ring

/-- **Sum of squared Fibonacci numbers from three consecutive squares.** Let $F_j$ denote the
$j$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every integer $n \ge 3$,
$$2 \sum_{j=1}^{n-2} F_j^2 = F_n^2 - F_{n-1}^2 - F_{n-2}^2.$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.5 (`fq-2024-belaggoun01132024-cor-3.5`). -/
theorem two_mul_sum_fib_sq {n : ℕ} (hn : 3 ≤ n) :
    2 * ∑ j ∈ Icc 1 (n - 2), (Nat.fib j : ℤ) ^ 2 =
      (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - 1) : ℤ) ^ 2 - (Nat.fib (n - 2) : ℤ) ^ 2 := by
  have h := fib_add_sq_eq le_rfl (show 2 ≤ n - 1 by omega)
  rw [show 1 + (n - 1) = n by omega, show n - 1 - 1 = n - 2 by omega] at h
  simp only [Nat.reduceAdd, Nat.fib_one, Nat.fib_two, one_pow, one_mul, Icc_self,
    sum_singleton] at h
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  omega

end MetaMathlibExt
