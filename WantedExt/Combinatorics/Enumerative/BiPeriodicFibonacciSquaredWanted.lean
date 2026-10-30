/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Combinatorial identities for the bi-periodic Fibonacci numbers squared

Statements from Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the
Bi-Periodic Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article
belaggoun01132024.

The bi-periodic Fibonacci numbers squared `q²_n` are defined by the paper's third-order
recurrence (1.1) (`biPeriodicFibonacciSq`). The weighted tilings of Section 2 are modelled on the
`2n` half-cells `0, …, 2n - 1` of an `n`-board, half-cell `h` lying in cell `⌊h/2⌋ + 1`: a
`(1/2, 1/2)`-fence at position `k` has its posts on half-cells `k` and `k + 2` (gap `k + 1`), a
tiling is a set `F` of fence positions with pairwise disjoint posts, and every half-cell not
covered by a post holds a half-square, of weight `a` in an odd cell and `b` in an even cell. Two
fences at positions `k`, `k + 1` interlock into a bifence; it is a free bifence (a metatile of its
own, covering two whole cells) exactly when `k` is even.

The statements with `a = b = 1` use `Nat.fib`; `ξ(n) = n % 2`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Fib.Basic

namespace MetaMathlibExt

open Finset

@[expose] public section

/-- The bi-periodic Fibonacci numbers squared `q²_n`: `q²_0 = 0`, `q²_1 = 1`, `q²_2 = a²`, and for
`n ≥ 3`, `q²_n = (a/b)(ab+1) q²_{n-1} + (ab+1) q²_{n-2} - (a/b) q²_{n-3}` for even `n`, with `a/b`
replaced by `b/a` for odd `n`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
def biPeriodicFibonacciSq {K : Type*} [Field K] (a b : K) : ℕ → K
  | 0 => 0
  | 1 => 1
  | 2 => a ^ 2
  | n + 3 =>
    if Even (n + 3) then
      a / b * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
        (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - a / b * biPeriodicFibonacciSq a b n
    else
      b / a * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
        (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - b / a * biPeriodicFibonacciSq a b n

/-- `q²_0 = 0`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_zero {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 0 = 0 := rfl

/-- `q²_1 = 1`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_one {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 1 = 1 := rfl

/-- `q²_2 = a²`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1. -/
@[simp]
theorem biPeriodicFibonacciSq_two {K : Type*} [Field K] (a b : K) :
    biPeriodicFibonacciSq a b 2 = a ^ 2 := rfl

/-- The recurrence (1.1) of `q²_{n+3}`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Definition 1.1, (1.1). -/
theorem biPeriodicFibonacciSq_add_three {K : Type*} [Field K] (a b : K) (n : ℕ) :
    biPeriodicFibonacciSq a b (n + 3) =
      if Even (n + 3) then
        a / b * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
          (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - a / b * biPeriodicFibonacciSq a b n
      else
        b / a * (a * b + 1) * biPeriodicFibonacciSq a b (n + 2) +
          (a * b + 1) * biPeriodicFibonacciSq a b (n + 1) - b / a * biPeriodicFibonacciSq a b n :=
  rfl

/-- The tilings of an `n`-board by half-squares and `(1/2, 1/2)`-fences, as the sets `F` of fence
positions `k < 2n - 2` (posts on half-cells `k` and `k + 2`) whose posts are pairwise disjoint.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilings (n : ℕ) : Finset (Finset ℕ) :=
  (range (2 * n - 2)).powerset.filter fun F => ∀ k ∈ F, k + 2 ∉ F

/-- The weight of the tiling with fence positions `F`: the product over the half-cells `h` not
covered by a fence post of `a` (half-square in an odd cell `⌊h/2⌋ + 1`) or `b` (even cell).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2. -/
def fenceTilingWeight {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) (F : Finset ℕ) : R :=
  ∏ h ∈ range (2 * n) \ (F ∪ F.image (· + 2)), if h / 2 % 2 = 0 then a else b

/-- `S_n`, the weighted number of tilings of an `n`-board by weighted half-squares and
`(1/2, 1/2)`-fences.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Section 2 (before Lemma 2.1). -/
def fenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ fenceTilings n, fenceTilingWeight a b n F

/-- `S_0 = 1` (the empty board).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
proof of Lemma 2.1. -/
@[simp]
theorem fenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) : fenceTilingSum a b 0 = 1 := by
  simp [fenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- `S_1 = a²` (two half-squares in cell `1`).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
proof of Theorem 2.2. -/
@[simp]
theorem fenceTilingSum_one {R : Type*} [CommSemiring R] (a b : R) : fenceTilingSum a b 1 = a ^ 2 := by
  simp [fenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton, prod_range_succ, sq]

/-- `C_n`, the weighted number of tilings with no bifence (no fence positions `k`, `k + 1`).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15. -/
def noBifenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ (fenceTilings n).filter (fun F => ∀ k ∈ F, k + 1 ∉ F), fenceTilingWeight a b n F

/-- `C_0 = 1`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15. -/
@[simp]
theorem noBifenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) :
    noBifenceTilingSum a b 0 = 1 := by
  simp [noBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- `R_n`, the weighted number of tilings with no free bifence (no fence positions `k`, `k + 1`
with `k` even).

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
def noFreeBifenceTilingSum {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) : R :=
  ∑ F ∈ (fenceTilings n).filter (fun F => ∀ k ∈ F, Even k → k + 1 ∉ F), fenceTilingWeight a b n F

/-- `R_0 = 1`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
@[simp]
theorem noFreeBifenceTilingSum_zero {R : Type*} [CommSemiring R] (a b : R) :
    noFreeBifenceTilingSum a b 0 = 1 := by
  simp [noFreeBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton]

/-- `R_1 = a²`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13. -/
@[simp]
theorem noFreeBifenceTilingSum_one {R : Type*} [CommSemiring R] (a b : R) :
    noFreeBifenceTilingSum a b 1 = a ^ 2 := by
  simp [noFreeBifenceTilingSum, fenceTilings, fenceTilingWeight, filter_singleton, prod_range_succ,
    sq]

/-- Lemma 2.1, even case: for even `n ≥ 2`,
`S_n = b² S_{n-1} + (2ab+1) S_{n-2} + 2ab ∑_{j=2}^{n/2} S_{n-2j} + 2b² ∑_{j=1}^{n/2-1} S_{n-2j-1}`.
The cases `n = 0, 1` (with `δ_{n,0}` and `S_{<0} = 0`) are `fenceTilingSum_zero`,
`fenceTilingSum_one`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`). -/
public theorem_wanted fenceTilingSum_even {R : Type*} [CommSemiring R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) :
    fenceTilingSum a b n =
      b ^ 2 * fenceTilingSum a b (n - 1) + (2 * a * b + 1) * fenceTilingSum a b (n - 2) +
        2 * a * b * ∑ j ∈ Icc 2 (n / 2), fenceTilingSum a b (n - 2 * j) +
        2 * b ^ 2 * ∑ j ∈ Icc 1 (n / 2 - 1), fenceTilingSum a b (n - 2 * j - 1)

/-- Lemma 2.1, odd case: for odd `n ≥ 3`,
`S_n = a² S_{n-1} + (2ab+1) S_{n-2} + 2ab ∑_{j=2}^{(n-1)/2} S_{n-2j}
  + 2a² ∑_{j=1}^{(n-1)/2} S_{n-2j-1}`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 2.1, (2.1) (`fq-2024-belaggoun01132024-lem-2.1`). -/
public theorem_wanted fenceTilingSum_odd {R : Type*} [CommSemiring R] (a b : R) {n : ℕ}
    (hn : 2 ≤ n) (ho : Odd n) :
    fenceTilingSum a b n =
      a ^ 2 * fenceTilingSum a b (n - 1) + (2 * a * b + 1) * fenceTilingSum a b (n - 2) +
        2 * a * b * ∑ j ∈ Icc 2 ((n - 1) / 2), fenceTilingSum a b (n - 2 * j) +
        2 * a ^ 2 * ∑ j ∈ Icc 1 ((n - 1) / 2), fenceTilingSum a b (n - 2 * j - 1)

/-- Theorem 2.2: for nonzero `a`, `b` and `n ≥ 0`, `q²_{n+1}` is the weighted number `S_n` of
tilings of an `n`-board by weighted half-squares and `(1/2, 1/2)`-fences.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Theorem 2.2 (`fq-2024-belaggoun01132024-thm-2.2`). -/
public theorem_wanted fenceTilingSum_eq_biPeriodicFibonacciSq {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    fenceTilingSum a b n = biPeriodicFibonacciSq a b (n + 1)

/-- Corollary 3.3: for `n ≥ 0`,
`F²_{n+1} = ∑_{i=0}^{⌊2n/3⌋} ∑_{j=0}^{i} C(i, j) C(2n-3i, j) 2^j`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.3 (`fq-2024-belaggoun01132024-cor-3.3`). -/
public theorem_wanted fib_succ_sq_eq_sum_choose_mul_choose (n : ℕ) :
    Nat.fib (n + 1) ^ 2 =
      ∑ i ∈ range (2 * n / 3 + 1), ∑ j ∈ range (i + 1),
        i.choose j * (2 * n - 3 * i).choose j * 2 ^ j

/-- Corollary 3.5: for `n ≥ 3`, `∑_{j=1}^{n-2} F²_j = (F²_n - F²_{n-1} - F²_{n-2})/2`, stated with
the factor `2` cleared.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.5 (`fq-2024-belaggoun01132024-cor-3.5`). -/
public theorem_wanted two_mul_sum_fib_sq {n : ℕ} (hn : 3 ≤ n) :
    2 * ∑ j ∈ Icc 1 (n - 2), (Nat.fib j : ℤ) ^ 2 =
      (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - 1) : ℤ) ^ 2 - (Nat.fib (n - 2) : ℤ) ^ 2

/-- Corollary 3.10: for `n ≥ 1`,
`F²_{n+1} - ξ(n+1) = ∑_{k=1}^{n} (n-k+1) F²_k = ∑_{k=1}^{n} k F²_{n-k+1}`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.10 (`fq-2024-belaggoun01132024-cor-3.10`). -/
public theorem_wanted fib_succ_sq_sub_parity_eq_sum {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, ((n - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2 ∧
      (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, (k : ℤ) * (Nat.fib (n - k + 1) : ℤ) ^ 2

/-- Corollary 3.12: for `n ≥ 2` and `m ≥ 1`,
`F²_{m+n} = F²_{m+1} F²_n + F²_m F²_{n-1} + 2 ∑_{i=1}^{m} F²_i ∑_{j=1}^{n-1} F²_j`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.12 (`fq-2024-belaggoun01132024-cor-3.12`). -/
public theorem_wanted fib_add_sq_eq {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    Nat.fib (m + n) ^ 2 =
      Nat.fib (m + 1) ^ 2 * Nat.fib n ^ 2 + Nat.fib m ^ 2 * Nat.fib (n - 1) ^ 2 +
        2 * (∑ i ∈ Icc 1 m, Nat.fib i ^ 2) * ∑ j ∈ Icc 1 (n - 1), Nat.fib j ^ 2

/-- Lemma 3.13: for nonzero `a`, `b` and `n ≥ 2`, the weighted number `R_n` of tilings with no
free bifence satisfies `R_n = (b/a)(ab+1) R_{n-1} + ab R_{n-2}` for even `n` and
`R_n = (a/b)(ab+1) R_{n-1} + ab R_{n-2}` for odd `n`. The initial values `R_0 = 1`, `R_1 = a²`
are `noFreeBifenceTilingSum_zero`, `noFreeBifenceTilingSum_one`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.13 (`fq-2024-belaggoun01132024-lem-3.13`). -/
public theorem_wanted noFreeBifenceTilingSum_rec {K : Type*} [Field K] {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    noFreeBifenceTilingSum a b n =
      (if Even n then b / a else a / b) * (a * b + 1) * noFreeBifenceTilingSum a b (n - 1) +
        a * b * noFreeBifenceTilingSum a b (n - 2)

/-- Lemma 3.15: for nonzero `a`, `b`, the weighted number `C_n` of tilings with no bifence is
`(a/b)^{ξ(n)} ∑_{i=0}^{⌊2n/3⌋} C(2n-2i, i) (ab)^{n-i}`.

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Lemma 3.15 (`fq-2024-belaggoun01132024-lem-3.15`). -/
public theorem_wanted noBifenceTilingSum_eq_sum_choose {K : Type*} [Field K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    noBifenceTilingSum a b n =
      (a / b) ^ (n % 2) *
        ∑ i ∈ range (2 * n / 3 + 1), ((2 * n - 2 * i).choose i : K) * (a * b) ^ (n - i)

end

end MetaMathlibExt
