/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Expand
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Glaisher's divisors and infinite products: wishlist

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6.

The *series-divisor* `(σ^A(k))_{k ≥ 1}` of a formal power series `A(q) = ∑ a(k) q^k`
is defined in the paper (Definition 1) by `n a(n) = ∑_{i=1}^n σ^A(i) a(n-i)` for
`n ≥ 1`, with `σ^A(r) = 0` unless `r` is a positive integer. No new definition is
introduced: each statement takes a sequence `s` together with that recurrence as a
hypothesis. Glaisher's divisor functions `d_A, …, d_G` and `σ̄₃`, `σ̃₃` are the divisor
sums displayed in the paper's introduction; they are written inline below (local
notation), with the paper's convention `σ(r) = 0` unless `r` is a positive integer.
Infinite sums over `j` are truncated at a bound past which every term vanishes.
-/

open PowerSeries
open scoped ArithmeticFunction.sigma

namespace MetaMathlibExt

@[expose] public section

/-- `σ(m)` as an integer. -/
local notation "σ₁" m:max => ((σ 1 m : ℕ) : ℤ)
/-- `σ(m / k)`, which is `0` unless `k ∣ m`. -/
local notation "σdiv" k:max m:max => (if k ∣ m then ((σ 1 (m / k) : ℕ) : ℤ) else 0)
/-- `d_B(m)`: sum of the odd divisors of `m`. -/
local notation "dB" m:max => ∑ d ∈ Nat.divisors m with Odd d, (d : ℤ)
/-- `d_C(m)`: sum of the even divisors of `m`. -/
local notation "dC" m:max => ∑ d ∈ Nat.divisors m with Even d, (d : ℤ)
/-- `d_D(m)`: sum of the divisors `d` of `m` with `m / d` odd. -/
local notation "dD" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ)
/-- `d_E(m)`: sum of the divisors `d` of `m` with `m / d` even. -/
local notation "dE" m:max => ∑ d ∈ Nat.divisors m with Even (m / d), (d : ℤ)
/-- `d_F(m) = ∑_{d ∣ m} (-1)^(d-1) d`. -/
local notation "dF" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (d - 1) * (d : ℤ)
/-- `d_G(m) = ∑_{d ∣ m} (-1)^(m/d-1) d`. -/
local notation "dG" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (m / d - 1) * (d : ℤ)
/-- `σ̄₃(m) = ∑_{d ∣ m, m/d odd} d³`. -/
local notation "σbar₃" m:max => ∑ d ∈ Nat.divisors m with Odd (m / d), (d : ℤ) ^ 3
/-- `σ̃₃(m) = ∑_{d ∣ m} (-1)^(d-1) d³`. -/
local notation "σtilde₃" m:max => ∑ d ∈ Nat.divisors m, (-1 : ℤ) ^ (d - 1) * (d : ℤ) ^ 3
/-- `p(m)`, the number of partitions of `m`. -/
local notation "pp" m:max => ((Fintype.card (Nat.Partition m) : ℕ) : ℤ)
/-- `p_o(m)`, the number of partitions of `m` into odd parts. -/
local notation "po" m:max => ((Finset.card (Nat.Partition.odds m) : ℕ) : ℤ)
/-- `p_d(m)`, the number of partitions of `m` into distinct parts. -/
local notation "pd" m:max => ((Finset.card (Nat.Partition.distincts m) : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `p_e(m)`, the number of partitions of `m` into even parts. -/
local notation "pe" m:max =>
  ((Finset.card (Finset.filter (fun π : Nat.Partition m => ∀ i ∈ π.parts, Even i)
    Finset.univ) : ℕ) : ℤ)
/-- `p̄(m)`, the number of overpartitions of `m`. -/
local notation "pbar" m:max => ((Nat.card (Nat.Overpartition m) : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `r_k(m)`: ordered representations of `m` as a sum of `k` squares of integers. -/
local notation "rsq" k:max m:max =>
  ((Set.ncard {x : Fin k → ℤ | ∑ i, x i ^ 2 = ((m : ℕ) : ℤ)} : ℕ) : ℤ)
set_option quotPrecheck false in
/-- `t_k(m)`: ordered representations of `m` as a sum of `k` triangular numbers. -/
local notation "ttri" k:max m:max =>
  ((Set.ncard {x : Fin k → ℕ | ∑ i, x i * (x i + 1) / 2 = m} : ℕ) : ℤ)

/-- Addition lemma: if `sA` and `sB` are series-divisors of `A` and `B`, then `sA + sB`
is a series-divisor of `A * B`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 2
(`jis-2024-24.1.6-lem-2`). -/
public theorem_wanted series_divisor_add_of_mul {R : Type*} [CommRing R]
    (A B : PowerSeries R) (sA sB : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, sA i * coeff (n - i) A)
    (hB : ∀ n : ℕ, (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, sB i * coeff (n - i) B) :
    ∀ n : ℕ, (n : R) * coeff n (A * B) =
      ∑ i ∈ Finset.Icc 1 n, (sA i + sB i) * coeff (n - i) (A * B)

/-- Calculus of series-divisors: if `s` is a series-divisor of `A`, then `-s` is one of
`A⁻¹` (any `B` with `A * B = 1`), `k ↦ (-1)^k s(k)` is one of `A(-q)`,
`k ↦ m s(k/m)` (zero unless `m ∣ k`) is one of `A(q^m)` for `m ≥ 1`, and `m s` is one
of `A^m`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Proposition 3
(`jis-2024-24.1.6-prop-3`). -/
public theorem_wanted series_divisor_calculus {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A) :
    (∀ B : PowerSeries R, A * B = 1 → ∀ n : ℕ,
      (n : R) * coeff n B = ∑ i ∈ Finset.Icc 1 n, -s i * coeff (n - i) B) ∧
    (∀ n : ℕ, (n : R) * coeff n (rescale (-1) A) =
      ∑ i ∈ Finset.Icc 1 n, (-1) ^ i * s i * coeff (n - i) (rescale (-1) A)) ∧
    (∀ (m : ℕ) (hm : m ≠ 0) (n : ℕ), (n : R) * coeff n (expand m hm A) =
      ∑ i ∈ Finset.Icc 1 n,
        (if m ∣ i then (m : R) * s (i / m) else 0) * coeff (n - i) (expand m hm A)) ∧
    (∀ m n : ℕ, (n : R) * coeff n (A ^ m) =
      ∑ i ∈ Finset.Icc 1 n, (m : R) * s i * coeff (n - i) (A ^ m))

/-- Recursion for powers: if `s` is a series-divisor of `A` and `a_m(k)` are the
coefficients of `A^m`, then `n a_m(n) = m ∑_{j=1}^n s(j) a_m(n-j)`. The printed
summand `σ^A(i)` is read as `σ^A(j)` (the summation index).

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Corollary 4
(`jis-2024-24.1.6-cor-4`). -/
public theorem_wanted series_divisor_pow_recursion {R : Type*} [CommRing R]
    (A : PowerSeries R) (s : ℕ → R)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (m n : ℕ) :
    (n : R) * coeff n (A ^ m) = (m : R) * ∑ j ∈ Finset.Icc 1 n, s j * coeff (n - j) (A ^ m)

/-- Glaisher's divisor functions are series-divisors of the generating functions of
`p`, `p_o`, `p_e`, `p̄`, `φ(q) = ∑_{k ∈ ℤ} q^{k²}`, `ψ(q) = ∑_{k ≥ 0} q^{k(k+1)/2}` and
`p_d`, stated as the defining recurrence for the coefficient sequences, together with
`d_C = 2 d_E`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 9
(`jis-2024-24.1.6-thm-9`). -/
public theorem_wanted glaisher_divisors_series_divisor_recurrences (n : ℕ) :
    (n : ℤ) * pp n = ∑ i ∈ Finset.Icc 1 n, (σ₁ i) * pp (n - i) ∧
    (n : ℤ) * po n = ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) ∧
    (dC n) = 2 * dE n ∧
    (n : ℤ) * pe n = ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) ∧
    (n : ℤ) * pbar n = ∑ i ∈ Finset.Icc 1 n, 2 * (dD i) * pbar (n - i) ∧
    (n : ℤ) * ((Set.ncard {k : ℤ | k ^ 2 = (n : ℤ)} : ℕ) : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (-1) ^ (i + 1) * 2 * (dD i) *
        ((Set.ncard {k : ℤ | k ^ 2 = ((n - i : ℕ) : ℤ)} : ℕ) : ℤ) ∧
    (n : ℤ) * ((Set.ncard {k : ℕ | k * (k + 1) / 2 = n} : ℕ) : ℤ) =
      ∑ i ∈ Finset.Icc 1 n, (dF i) * ((Set.ncard {k : ℕ | k * (k + 1) / 2 = n - i} : ℕ) : ℤ) ∧
    (n : ℤ) * pd n = ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i)

/-- Recurrences for `p_e`, `p_d` and `p̄` in terms of Glaisher's divisors and `σ`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 10
(`jis-2024-24.1.6-thm-10`). -/
public theorem_wanted glaisher_partition_recurrences (n : ℕ) :
    ((n : ℤ) * pe n = ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dC i) * pe (n - i) =
        2 * ∑ i ∈ Finset.Icc 1 n, (σdiv 2 i) * pe (n - i)) ∧
    ((n : ℤ) * pd n = ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dB i) * po (n - i) = ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i) ∧
      ∑ i ∈ Finset.Icc 1 n, (dG i) * pd (n - i) =
        ∑ i ∈ Finset.Icc 1 n, ((σ₁ i) - 2 * σdiv 2 i) * pd (n - i)) ∧
    ((n : ℤ) * pbar n = 2 * ∑ i ∈ Finset.Icc 1 n, (dD i) * pbar (n - i) ∧
      2 * ∑ i ∈ Finset.Icc 1 n, (dD i) * pbar (n - i) =
        2 * ∑ i ∈ Finset.Icc 1 n, ((σ₁ i) - σdiv 2 i) * pbar (n - i))

/-- Recurrences for `r_m(n)` (ordered sums of `m` squares of integers) and `t_m(n)`
(ordered sums of `m` triangular numbers `k(k+1)/2`, `k ≥ 0`).

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 11
(`jis-2024-24.1.6-thm-11`). -/
public theorem_wanted sum_squares_triangular_power_recurrences (m : ℕ) (hm : 0 < m)
    (n : ℕ) :
    (n : ℤ) * rsq m n = (m : ℤ) * ∑ j ∈ Finset.Icc 1 n,
      2 * (-1) ^ (j + 1) * ((σ₁ j) - σdiv 2 j) * rsq m (n - j) ∧
    (n : ℤ) * ttri m n = (m : ℤ) * ∑ j ∈ Finset.Icc 1 n,
      ((σ₁ j) - 4 * σdiv 2 j) * ttri m (n - j)

open Classical in
/-- Six recursions for `d_D`, `d_F`, `σ`, `σ̄₃` and `σ̃₃` coming from `φ(q)` and `ψ(q)`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 14
(`jis-2024-24.1.6-thm-14`). -/
public theorem_wanted glaisher_theta_divisor_recursions (n : ℕ) (hn : 0 < n) :
    (dD n) + 2 * ∑ j ∈ Finset.Icc 1 n, (-1) ^ j * dD (n - j ^ 2) =
      (if IsSquare n then (-1) ^ (n - 1) * (n : ℤ) else 0) ∧
    ∑ j ∈ Finset.range (n + 1), dF (n - j * (j + 1) / 2) =
      (if ∃ j : ℕ, j * (j + 1) / 2 = n then (n : ℤ) else 0) ∧
    8 * ∑ j ∈ Finset.Ioo 0 n, (-1) ^ (j + 1) * (dD j) * ((σ₁ (n - j)) - 4 * σdiv 4 (n - j)) =
      (n : ℤ) * ((σ₁ n) - 4 * σdiv 4 n) + (-1) ^ n * dD n ∧
    4 * ∑ j ∈ Finset.Icc 1 n, (dF j) * σ₁ (2 * n + 1 - 2 * j) = (n : ℤ) * σ₁ (2 * n + 1) ∧
    16 * ∑ j ∈ Finset.Ioo 0 n, (dD j) * σtilde₃ (n - j) = (dD n) - (n : ℤ) * σtilde₃ n ∧
    8 * ∑ j ∈ Finset.Icc 1 n, (dF j) * σbar₃ (n + 1 - j) = (n : ℤ) * σbar₃ (n + 1)

/-- Power recursion lemma: for a unit `A` of `K⟦X⟧` and nonzero integers `u`, `v`,
the coefficients `a_u`, `a_v` of `A^u` and `A^v` satisfy
`∑_{k=0}^n (n - (u/v + 1) k) a_u(n-k) a_v(k) = 0`. Restricted to invertible `A`, which
negative powers require.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem_wanted power_coeff_convolution_zpow {K : Type*} [Field K] [CharZero K]
    (A : (PowerSeries K)ˣ) (u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) * coeff (n - k) ((A ^ u : (PowerSeries K)ˣ) : PowerSeries K) *
        coeff k ((A ^ v : (PowerSeries K)ˣ) : PowerSeries K) = 0

/-- Power recursion lemma for positive exponents and an arbitrary power series `A`:
`∑_{k=0}^n (n - (u/v + 1) k) a_u(n-k) a_v(k) = 0`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 17
(`jis-2024-24.1.6-lem-17`). -/
public theorem_wanted power_coeff_convolution_pow {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((n : K) - ((u : K) / v + 1) * k) * coeff (n - k) (A ^ u) * coeff k (A ^ v) = 0

/-- Six divisor-function recursions obtained from the power recursion lemma.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 19
(`jis-2024-24.1.6-thm-19`). -/
public theorem_wanted glaisher_power_recursion_divisor_identities (n : ℕ) (hn : 0 < n) :
    2 * (n : ℤ) * σ₁ (2 * n + 1) = ∑ j ∈ Finset.Icc 1 n,
      (5 * (j : ℤ) * (j + 1) - 2 * n) * σ₁ (2 * n + 1 - j * (j + 1)) ∧
    (n : ℤ) * ((σ₁ n) - 4 * σdiv 4 n) - 2 * ∑ j ∈ Finset.Icc 1 n,
      (5 * (j : ℤ) ^ 2 - n) * ((σ₁ (n - j ^ 2)) - 4 * σdiv 4 (n - j ^ 2)) =
      (if IsSquare n then (n : ℤ) else 0) ∧
    (n : ℤ) * σbar₃ (n + 1) = ∑ j ∈ Finset.Icc 1 (n + 1),
      (9 * (((j * (j + 1) / 2 : ℕ)) : ℤ) - n) * σbar₃ (n + 1 - j * (j + 1) / 2) ∧
    (n : ℤ) * (σtilde₃ n) - 2 * ∑ j ∈ Finset.Icc 1 n,
      (-1) ^ j * (9 * (j : ℤ) ^ 2 - n) * σtilde₃ (n - j ^ 2) =
      (if IsSquare n then (-1) ^ (n - 1) * (n : ℤ) else 0) ∧
    ∑ j ∈ Finset.range (n + 2), (3 * (j : ℤ) - n) * (σ₁ (2 * j + 1)) * σbar₃ (n + 1 - j) = 0 ∧
    (n : ℤ) * ((σtilde₃ n) + (-1) ^ n * ((σ₁ n) - 4 * σdiv 4 n)) =
      8 * ∑ j ∈ Finset.Ioo 0 n,
        (3 * (j : ℤ) - n) * (-1) ^ j * ((σ₁ j) - 4 * σdiv 4 j) * σtilde₃ (n - j)

open Classical in
/-- Four congruences for sums of `σ` and `σ̄₃` over shifts by squares and triangular
numbers.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 20
(`jis-2024-24.1.6-thm-20`). -/
public theorem_wanted glaisher_divisor_sum_congruences (n : ℕ) (hn : 0 < n) :
    (¬ 5 ∣ n → ∑ j ∈ Finset.range (n + 1), σ₁ (2 * n + 1 - j * (j + 1)) ≡ 0 [ZMOD 5]) ∧
    ∑ j ∈ Finset.range (n + 1), σ₁ (n - j * (j + 1) / 2) ≡
      (if ∃ k : ℕ, k * (k + 1) / 2 = n then (n : ℤ) else 0) [ZMOD 4] ∧
    (¬ 5 ∣ n → (n % 4 = 3 ∨ n % 4 = 2) →
      (σ₁ n) + 2 * ∑ j ∈ Finset.Icc 1 n, σ₁ (n - j ^ 2) ≡ 0 [ZMOD 5]) ∧
    (Nat.Coprime n 3 →
      ∑ j ∈ Finset.range (n + 2), σbar₃ (n + 1 - j * (j + 1) / 2) ≡ 0 [ZMOD 9])

open Classical in
/-- For `n ≥ 1`, `∑_{j ≥ 0} σ(2n + 1 - j(j+1))` is `1` mod 5 when `n = 5k(k+1)/2` for
some `k`, and `0` mod 5 otherwise.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 23
(`jis-2024-24.1.6-thm-23`). -/
public theorem_wanted sigma_triangular_shift_sum_mod_five (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ Finset.range (n + 1), σ₁ (2 * n + 1 - j * (j + 1)) ≡
      (if ∃ k : ℕ, 5 * k * (k + 1) / 2 = n then 1 else 0) [ZMOD 5]

/-- Convolution lemma: if `A * B = 1` and `s` is a series-divisor of `A` (with
`s 0 = 0`), then `s(n) = ∑_{i=0}^n (n-i) a(n-i) b(i)` and
`∑_{i=1}^n s(n-i) s(i) = -∑_{i=1}^n i (n-i) a(n-i) b(i)`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Lemma 25
(`jis-2024-24.1.6-lem-25`). -/
public theorem_wanted series_divisor_inverse_convolution {R : Type*} [CommRing R]
    (A B : PowerSeries R) (hAB : A * B = 1) (s : ℕ → R) (hs0 : s 0 = 0)
    (hA : ∀ n : ℕ, (n : R) * coeff n A = ∑ i ∈ Finset.Icc 1 n, s i * coeff (n - i) A)
    (n : ℕ) :
    s n = ∑ i ∈ Finset.range (n + 1), ((n - i : ℕ) : R) * coeff (n - i) A * coeff i B ∧
    ∑ i ∈ Finset.Icc 1 n, s (n - i) * s i =
      -∑ i ∈ Finset.Icc 1 n, ((i * (n - i) : ℕ) : R) * coeff (n - i) A * coeff i B

/-- Two formulas linking overpartitions and `d_D`:
`2 d_D(n) = 2(σ(n) - σ(n/2)) = n p̄(n) + 2 ∑_{i ≥ 1} (-1)^i (n - i²) p̄(n - i²)` and
`2 ∑_{i=1}^n d_D(n-i) d_D(i) = ∑_{i ≥ 1} (-1)^{i+1} i² (n - i²) p̄(n - i²)`, the sums over
`i` running over `i² ≤ n`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 26
(`jis-2024-24.1.6-thm-26`). -/
public theorem_wanted overpartition_glaisher_dD_formulas (n : ℕ) :
    (2 * (dD n) = 2 * ((σ₁ n) - σdiv 2 n) ∧
      2 * ((σ₁ n) - σdiv 2 n) = (n : ℤ) * pbar n +
        2 * ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
          (-1) ^ i * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)) ∧
    2 * ∑ i ∈ Finset.Icc 1 n, (dD (n - i)) * dD i =
      ∑ i ∈ Finset.Icc 1 n with i ^ 2 ≤ n,
        (-1) ^ (i + 1) * (i : ℤ) ^ 2 * ((n : ℤ) - (i : ℤ) ^ 2) * pbar (n - i ^ 2)

/-- Ramanujan's congruence `p(5m+4) ≡ 0 (mod 5)` for all `m` is equivalent to
`∑_{i ≥ 1} σ(i) σ(5m+1-i) ≡ 0 (mod 5)` for all `m`.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 28
(`jis-2024-24.1.6-thm-28`). -/
public theorem_wanted partition_mod_five_iff_sigma_convolution :
    (∀ m : ℕ, Fintype.card (Nat.Partition (5 * m + 4)) ≡ 0 [MOD 5]) ↔
      ∀ m : ℕ, ∑ i ∈ Finset.Icc 1 (5 * m), σ 1 i * σ 1 (5 * m + 1 - i) ≡ 0 [MOD 5]

/-- `p̄(4m+3) ≡ 0 (mod 8)` for all `m` is equivalent to
`∑_{i ≥ 1} d_D(i) d_D(4m-i) ≡ 0 (mod 4)` for all `m`, where `p̄` counts overpartitions.

Source: Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite
Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 30
(`jis-2024-24.1.6-thm-30`). -/
public theorem_wanted overpartition_mod_eight_iff_dD_convolution :
    (∀ m : ℕ, Nat.card (Nat.Overpartition (4 * m + 3)) ≡ 0 [MOD 8]) ↔
      ∀ m : ℕ, ∑ i ∈ Finset.Ioo 0 (4 * m), (dD i) * dD (4 * m - i) ≡ 0 [ZMOD 4]

end

end MetaMathlibExt
