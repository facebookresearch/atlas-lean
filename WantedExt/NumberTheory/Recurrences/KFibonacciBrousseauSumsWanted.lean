/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

/-!
# Brousseau sums of k-Fibonacci numbers

Statements from Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau
Sums*, Journal of Integer Sequences 27 (2024), Article 24.6.4.

The `k`-Fibonacci numbers `F_{k,n}` (`F_{k,0} = 0`, `F_{k,1} = 1`,
`F_{k,n} = k F_{k,n-1} + F_{k,n-2}`) are the Lucas sequence `U(k, -1)`,
`lucasU ⟨k, -1, _⟩`; the Fibonacci, Lucas and Pell numbers are `Nat.fib`, `lucasNumber` and
`pellNumber`, and the Pell–Lucas numbers `Q_n` (`Q_0 = Q_1 = 2`) are `lucasV ⟨2, -1, _⟩`.
The paper takes `k` a positive integer; the identities are stated for every nonzero integer
`k` (every integer `k` in Theorem 1).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The numbers `A_k^(p)` of Definition 1: `A_k^(0) = 1` and
`A_k^(p) = (2/k) ∑_{j=1}^{⌈p/2⌉} binom(p, 2j-1) A_k^(p-2j+1)` for `p ≥ 1` (written with
`p + 1` in place of `p` and `j + 1` in place of `j`).

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
def brousseauA (k : ℚ) : ℕ → ℚ
  | 0 => 1
  | p + 1 => 2 / k * ∑ j ∈ Finset.range ((p + 2) / 2),
      ((p + 1).choose (2 * j + 1) : ℚ) * brousseauA k (p - 2 * j)
decreasing_by omega

/-- `A_k^(0) = 1`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_zero (k : ℚ) : brousseauA k 0 = 1 := by
  rw [brousseauA]

/-- `A_k^(1) = 2/k`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_one (k : ℚ) : brousseauA k 1 = 2 / k := by
  rw [brousseauA]
  simp [brousseauA_zero]

/-- `A_k^(2) = 8/k²`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 1. -/
theorem brousseauA_two (k : ℚ) : brousseauA k 2 = 8 / k ^ 2 := by
  rw [brousseauA]
  simp [brousseauA_one]
  ring

/-- The coefficient polynomial `C_k^(p)(n) = ∑_{r=0}^p (-1)^r A_k^(r) binom(p, r) n^(p-r)`
of Definition 5 (with `0^0 = 1`, which gives the paper's separate value
`C_k^(p)(0) = (-1)^p A_k^(p)`).

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
def brousseauCoeff (k : ℚ) (p : ℕ) (n : ℚ) : ℚ :=
  ∑ r ∈ Finset.range (p + 1), (-1) ^ r * brousseauA k r * (p.choose r : ℚ) * n ^ (p - r)

/-- `C_k^(0)(n) = 1`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_zero (k n : ℚ) : brousseauCoeff k 0 n = 1 := by
  simp [brousseauCoeff, brousseauA_zero]

/-- `C_k^(1)(n) = n - 2/k`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Definition 5. -/
theorem brousseauCoeff_one (k n : ℚ) : brousseauCoeff k 1 n = n - 2 / k := by
  simp [brousseauCoeff, Finset.sum_range_succ, brousseauA_zero, brousseauA_one]
  ring

/-- **Theorem 1.** For all integers `k`, `n ≥ 0` and `p ≥ 1`,
`F_{k,n} = n^p + ∑_{i=1}^n (k i^p - 2 ∑_{j=1}^{⌈p/2⌉} binom(p, 2j-1) i^(p-2j+1)) F_{k,n-i}`.
Stated for all integers `k` and `n ≥ 0` (paper: `k ≥ 1`, `n ≥ 1`); `⌈p/2⌉ = (p + 1) / 2`, and the
exponent `p - 2j + 1` is written `p + 1 - 2j` (nonnegative for `j ≤ ⌈p/2⌉`).

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 1 (`jis-2024-24.6.4-thm-1`). -/
public theorem_wanted kFibonacci_eq_pow_add_convolution (k : ℤ) (n p : ℕ) (hp : 1 ≤ p) :
    lucasU ⟨k, -1, by decide⟩ n = (n : ℤ) ^ p +
      ∑ i ∈ Finset.Icc 1 n, (k * (i : ℤ) ^ p -
        2 * ∑ j ∈ Finset.Icc 1 ((p + 1) / 2),
          (p.choose (2 * j - 1) : ℤ) * (i : ℤ) ^ (p + 1 - 2 * j)) *
        lucasU ⟨k, -1, by decide⟩ (n - i)

/-- **Theorem 4.** With `T_{k,n}^(p) = ∑_{i=0}^n i^p F_{k,n-i}` (Eq. (14), `0^0 = 1`),
`k T_{k,n}^(p) = A_k^(p) F_{k,n+1} + ∑_{r=0}^p A_k^(r) binom(p, r) ((-1)^(p-r) F_{k,n} - n^(p-r))`
for all `p, n ≥ 0`. Stated for every nonzero integer `k`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 4 (`jis-2024-24.6.4-thm-4`). -/
public theorem_wanted kFibonacci_power_convolution (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (n - i) =
      brousseauA k p * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        ∑ r ∈ Finset.range (p + 1), brousseauA k r * (p.choose r : ℚ) *
          ((-1) ^ (p - r) * lucasU ⟨k, -1, by decide⟩ n - (n : ℚ) ^ (p - r))

/-- **Theorem 6.** With `S_{k,n}^(p) = ∑_{i=0}^n i^p F_{k,i}` (Eq. (24), `0^0 = 1`),
`k S_{k,n}^(p) = C_k^(p)(n) F_{k,n+1} + C_k^(p)(n+1) F_{k,n} - C_k^(p)(0)` for all `p, n ≥ 0`.
Stated for every nonzero integer `k`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 6 (`jis-2024-24.6.4-thm-6`). -/
public theorem_wanted kFibonacci_brousseau_sum (k : ℤ) (hk : k ≠ 0) (n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ i =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ n - brousseauCoeff k p 0

/-- **Corollary 9.** For odd `m` and all `p, n ≥ 0`,
`L_m ∑_{i=1}^n i^p F_{mi} = C_{L_m}^(p)(n) F_{m(n+1)} + C_{L_m}^(p)(n+1) F_{mn} -
C_{L_m}^(p)(0) F_m`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 9 (`jis-2024-24.6.4-cor-9`). -/
public theorem_wanted fibonacci_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasNumber m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * Nat.fib (m * i) =
      brousseauCoeff (lucasNumber m) p n * Nat.fib (m * (n + 1)) +
        brousseauCoeff (lucasNumber m) p (n + 1) * Nat.fib (m * n) -
        brousseauCoeff (lucasNumber m) p 0 * Nat.fib m

/-- **Corollary 10.** For odd `m` and all `p, n ≥ 0`, with `P` the Pell and `Q` the Pell–Lucas
numbers (`Q_0 = Q_1 = 2`),
`Q_m ∑_{i=1}^n i^p P_{mi} = C_{Q_m}^(p)(n) P_{m(n+1)} + C_{Q_m}^(p)(n+1) P_{mn} -
C_{Q_m}^(p)(0) P_m`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Corollary 10
(`jis-2024-24.6.4-cor-10`). -/
public theorem_wanted pell_brousseau_sum_mul_odd (m : ℕ) (hm : Odd m) (n p : ℕ) :
    (lucasV ⟨2, -1, by decide⟩ m : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * pellNumber (m * i) =
      brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p n * pellNumber (m * (n + 1)) +
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p (n + 1) * pellNumber (m * n) -
        brousseauCoeff (lucasV ⟨2, -1, by decide⟩ m) p 0 * pellNumber m

/-- **Theorem 11.** For all `m, p, n ≥ 0`,
`k ∑_{i=1}^n i^p F_{k,m+i} = C_k^(p)(n) F_{k,m+n+1} + C_k^(p)(n+1) F_{k,m+n} -
C_k^(p)(0) F_{k,m+1} - C_k^(p)(1) F_{k,m}`. Stated for every nonzero integer `k`.

Source: Prabha Sivaraman Nair and Rejikumar Karunakaran, *On k-Fibonacci Brousseau Sums*,
Journal of Integer Sequences 27 (2024), Article 24.6.4, Theorem 11 (`jis-2024-24.6.4-thm-11`). -/
public theorem_wanted kFibonacci_shifted_brousseau_sum (k : ℤ) (hk : k ≠ 0) (m n p : ℕ) :
    (k : ℚ) * ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ p * lucasU ⟨k, -1, by decide⟩ (m + i) =
      brousseauCoeff k p n * lucasU ⟨k, -1, by decide⟩ (m + n + 1) +
        brousseauCoeff k p (n + 1) * lucasU ⟨k, -1, by decide⟩ (m + n) -
        brousseauCoeff k p 0 * lucasU ⟨k, -1, by decide⟩ (m + 1) -
        brousseauCoeff k p 1 * lucasU ⟨k, -1, by decide⟩ m

end

end MetaMathlibExt
