/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors

namespace MetaMathlibExt

@[expose] public section

/-- A product comparison for `1 - 1/x`: let `(z_i)` and `(y_i)` be non-decreasing `k`-tuples of
reals greater than one with `∏_{i ≤ l} z_i ≤ ∏_{i ≤ l} y_i` for all `1 ≤ l ≤ k` (10). Then
`∏_{i=1}^k (1 - 1/z_i) ≤ ∏_{i=1}^k (1 - 1/y_i)`, with equality if and only if `z_i = y_i` for
all `i`. Tuples are indexed by `Fin k` (`i = 0, …, k-1`), and the prefix condition is stated for
every `l ≤ k` (the case `l = 0` is the empty product).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 2 (`integers-2024-A114-lem-2`), citing its reference [4]. -/
public theorem_wanted prod_one_sub_inv_le_of_prefix_prod_le (k : ℕ) (z y : Fin k → ℝ)
    (hz : Monotone z) (hy : Monotone y) (hz1 : ∀ i, 1 < z i) (hy1 : ∀ i, 1 < y i)
    (hprefix : ∀ l ≤ k, ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), z i ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < l), y i) :
    ∏ i, (1 - 1 / z i) ≤ ∏ i, (1 - 1 / y i) ∧
      (∏ i, (1 - 1 / z i) = ∏ i, (1 - 1 / y i) ↔ z = y)

/-- First-element bounds for HBC-admissible `k`-tuples for `1/2`: let `y_1 < ⋯ < y_k` be positive
integers with `∏_{i=1}^k (1 - 1/y_i) ≤ 1/2 < ∏_{i=1}^{k-1} (1 - 1/y_i)` (32). Then
(i) `y_1 ≤ k + 1`; (ii) if all `y_i` are odd, `y_1 < 2(k + 3)/3`; (iii) if all `y_i` are prime,
`y_1 < 3k/7 + 3` (33). The tuple is strictly increasing, as in the source's Theorem 1, whose
tuples (18) the source calls HBC-admissible; it is indexed by `Fin k` with `k ≥ 1`, `y_1` being
`y ⟨0, hk⟩`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 5 (`integers-2024-A114-lem-5`). -/
public theorem_wanted hbcAdmissible_half_first_le (k : ℕ) (hk : 0 < k) (y : Fin k → ℕ)
    (hmono : StrictMono y) (hpos : ∀ i, 0 < y i)
    (hle : ∏ i, (1 - 1 / (y i : ℚ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < k - 1),
      (1 - 1 / (y i : ℚ))) :
    y ⟨0, hk⟩ ≤ k + 1 ∧
      ((∀ i, Odd (y i)) → (y ⟨0, hk⟩ : ℚ) < 2 * (k + 3) / 3) ∧
      ((∀ i, (y i).Prime) → (y ⟨0, hk⟩ : ℚ) < 3 * k / 7 + 3)

/-- The smallest prime divisor `p_1` of an odd perfect number `N` with `m` distinct prime
divisors satisfies `p_1 < 3m/7 + 3` (36). An odd perfect number is `Odd N ∧ N.Perfect`,
`p_1 = N.minFac` and `m = N.primeFactors.card`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 6 (`integers-2024-A114-lem-6`). -/
public theorem_wanted oddPerfect_minFac_lt (N : ℕ) (hodd : Odd N) (hperf : N.Perfect) :
    (N.minFac : ℚ) < 3 * N.primeFactors.card / 7 + 3

/-- Sylvester (1888), quoted as Lemma 1 (ii): an odd perfect number has at least five distinct
prime divisors. Odd perfect numbers are `Odd N ∧ N.Perfect`; item (i) of the lemma (Euler's form)
is the proved `MetaMathlibExt.euler_odd_perfect_form`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (ii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_five_le_card_primeFactors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) : 5 ≤ N.primeFactors.card

/-- Dickson (1913), quoted as Lemma 1 (iii): for every `m`, only finitely many odd perfect numbers
have exactly `m` distinct prime divisors.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (iii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted finite_setOf_oddPerfect_card_primeFactors_eq (m : ℕ) :
    {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = m}.Finite

/-- Steuerwald (1937), quoted as Lemma 1 (iv): the even exponents of an odd perfect number are not
all equal to two, i.e. some prime divisor has an even exponent different from `2`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (iv) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_even_factorization_ne_two (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ N.factorization p ≠ 2

/-- McDaniel (1970), quoted as Lemma 1 (v): an odd perfect number below `10 ^ 9118` has a prime
divisor whose exponent is at least six.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (v) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_six_le_factorization_of_lt (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) (hN : N < 10 ^ 9118) :
    ∃ p ∈ N.primeFactors, 6 ≤ N.factorization p

/-- Kishore (1981) and Hagis (1983), quoted as Lemma 1 (vi): an odd perfect number not divisible by
three has at least eleven distinct prime divisors.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (vi) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_eleven_le_card_primeFactors_of_not_three_dvd (N : ℕ)
    (hodd : Odd N) (hperf : N.Perfect) (h3 : ¬ 3 ∣ N) : 11 ≤ N.primeFactors.card

/-- Nielsen (2015), quoted as Lemma 1 (vii): an odd perfect number has at least ten distinct prime
divisors, and at least twelve if it is not divisible by three.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (vii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_ten_le_card_primeFactors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    10 ≤ N.primeFactors.card ∧ (¬ 3 ∣ N → 12 ≤ N.primeFactors.card)

/-- Zelinsky (2021), quoted as Lemma 1 (viii): an odd perfect number with `m` distinct prime
divisors has a prime divisor less than `(m - 1) / 2` (real division; equivalently the smallest
prime divisor `N.minFac` is below it).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (viii) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_minFac_lt_card_sub_one_div_two (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    (N.minFac : ℚ) < ((N.primeFactors.card : ℚ) - 1) / 2

/-- Ochem and Rao (2012), quoted as Lemma 1 (ix): every odd perfect number exceeds `10 ^ 1500`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (ix) (`integers-2024-A114-lem-1`). -/
public theorem_wanted ten_pow_fifteen_hundred_lt_of_oddPerfect (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) : 10 ^ 1500 < N

/-- Goto and Ohno (2008) and Iannucci (1999, 2000), quoted as Lemma 1 (x): the largest, second
largest and third largest prime divisors of an odd perfect number are at least `10 ^ 8`, `10 ^ 4`
and `100`. Stated as the existence of three distinct prime divisors `p ≥ 10 ^ 8`, `q ≥ 10 ^ 4`,
`r ≥ 100`, which is equivalent: the `j`-th largest prime divisor is at least the `j`-th largest of
`p, q, r`, and conversely the three largest prime divisors are such a triple.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (x) (`integers-2024-A114-lem-1`). -/
public theorem_wanted oddPerfect_exists_three_large_prime_divisors (N : ℕ) (hodd : Odd N)
    (hperf : N.Perfect) :
    ∃ p ∈ N.primeFactors, ∃ q ∈ N.primeFactors, ∃ r ∈ N.primeFactors,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ 10 ^ 8 ≤ p ∧ 10 ^ 4 ≤ q ∧ 100 ≤ r

/-- Calibrating numbers for `a/(a + d)`: with `α = (a + d)/d`, `n_i = 1 + α^{2^{i-1}}` for
`1 ≤ i < k` and `n_k = α^{2^{k-1}}` (Definition 3). Then `∏_{i=1}^k (1 - 1/n_i) = a/(a + d)` (15),
`∏_{i=1}^j n_i = (d/a)(α^{2^j} - 1)` for `1 ≤ j < k` (16), and
`∏_{i=1}^k n_i = (d/a)(α^{2^k} - α^{2^{k-1}})` (17). Stated over `ℚ` for positive integers `a`, `d`
(coprimality is not needed) and `k ≥ 1`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 3. -/
public theorem_wanted hbcCalibrating_prod_identities (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hk : 1 ≤ k) :
    let α : ℚ := (a + d) / d
    let n : ℕ → ℚ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (1 - 1 / n i) = (a : ℚ) / (a + d) ∧
      (∀ j, 1 ≤ j → j < k → ∏ i ∈ Finset.Icc 1 j, n i = (d / a) * (α ^ 2 ^ j - 1)) ∧
      ∏ i ∈ Finset.Icc 1 k, n i = (d / a) * (α ^ 2 ^ k - α ^ 2 ^ (k - 1))

/-- Main theorem: let `a, d` be coprime positive integers and `y_1 < ⋯ < y_k` positive integers
with `∏_{i=1}^k (1 - 1/y_i) ≤ a/(a + d) < ∏_{i=1}^{k-1} (1 - 1/y_i)` (18). With `α = (a + d)/d`
and the calibrating numbers `n_i` of Definition 3, some `κ ∈ [1, k]` has
`∏_{i ≤ κ} y_i ≤ ∏_{i ≤ κ} n_i` (19); and if `κ_max` is the largest such `κ`, then
`a ∏_{i=1}^k y_i ≤ d^η F_k(α(κ_max))` (21), where `F_k(x) = x^{2^k} - x^{2^{k-1}}`,
`α(κ) = α d^{1/2^κ}` for `κ < k`, `α(k) = α` (20), and `η = 1` if `κ_max = k`, else `0`.
Tuples are indexed `1, …, k` as functions `ℕ → ℕ`; `κ_max` is characterized by (19) holding at
`κ` and failing at every larger `κ' ≤ k`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Theorem 1. -/
public theorem_wanted hbcAdmissible_exists_prefix_le_and_prod_le (a d k : ℕ) (ha : 0 < a)
    (hd : 0 < d) (hcop : Nat.Coprime a d) (hk : 1 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    let α : ℝ := (a + d) / d
    let n : ℕ → ℝ := fun i => if i < k then 1 + α ^ 2 ^ (i - 1) else α ^ 2 ^ (k - 1)
    let ακ : ℕ → ℝ := fun κ => if κ < k then α * (d : ℝ) ^ ((1 : ℝ) / 2 ^ κ) else α
    (∃ κ ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 κ, (y i : ℝ) ≤ ∏ i ∈ Finset.Icc 1 κ, n i) ∧
      ∀ κ ∈ Finset.Icc 1 k, ∏ i ∈ Finset.Icc 1 κ, (y i : ℝ) ≤ ∏ i ∈ Finset.Icc 1 κ, n i →
        (∀ κ' ∈ Finset.Icc 1 k, κ < κ' →
          ∏ i ∈ Finset.Icc 1 κ', n i < ∏ i ∈ Finset.Icc 1 κ', (y i : ℝ)) →
        a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          (if κ = k then (d : ℝ) else 1) * (ακ κ ^ 2 ^ k - ακ κ ^ 2 ^ (k - 1))

/-- Under the hypotheses of Theorem 1,
`a ∏_{i=1}^k y_i ≤ ((a + d)/√d)^{2^k} - ((a + d)/√d)^{2^{k-1}}` (26).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 1. -/
public theorem_wanted hbcAdmissible_prod_le_sqrt (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 1 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / Real.sqrt d) ^ 2 ^ k - ((a + d) / Real.sqrt d) ^ 2 ^ (k - 1)

/-- Under the hypotheses of Theorem 1 with `k ≥ 2`, unless `y_1 = ⌊1 + α⌋` (`α = (a + d)/d`),
`a ∏_{i=1}^k y_i ≤ ((a + d)/d^{3/4})^{2^k} - ((a + d)/d^{3/4})^{2^{k-1}}` (27).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Corollary 2. -/
public theorem_wanted hbcAdmissible_prod_le_of_ne_floor (a d k : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hcop : Nat.Coprime a d) (hk : 2 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ (a : ℝ) / (a + d))
    (hlt : (a : ℝ) / (a + d) < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (hy1 : y 1 ≠ ⌊1 + ((a : ℝ) + d) / d⌋₊) :
    a * ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ k - ((a + d) / (d : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ^ (k - 1)

/-- For `k ≥ 3` and every HBC-admissible `k`-tuple `y_1 < ⋯ < y_k` for `7/10`
(`∏_{i=1}^k (1 - 1/y_i) ≤ 7/10 < ∏_{i=1}^{k-1} (1 - 1/y_i)`),
`∏_{i=1}^k y_i ≤ (2/7)((√15)^{2^k} - (√15)^{2^{k-1}})` (31). The sharpness remark is not stated.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 4. -/
public theorem_wanted hbcAdmissible_seven_tenths_prod_le (k : ℕ) (hk : 3 ≤ k) (y : ℕ → ℕ) (hy0 : 0 < y 1) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 7 / 10)
    (hlt : 7 / 10 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ))) :
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      2 / 7 * (Real.sqrt 15 ^ 2 ^ k - Real.sqrt 15 ^ 2 ^ (k - 1))

/-- Let `p_1 < ⋯ < p_k` be primes with `∏_{i=1}^k (1 - 1/p_i) ≤ 1/2 < ∏_{i=1}^{k-1} (1 - 1/p_i)`
(37) and `p_1 ≥ 5`. With `F_k(x) = x^{2^k} - x^{2^{k-1}}`: `∏ p_i ≤ F_k(√(8/3^{7/8}))` (38);
if `6 ≤ p_1 < 18`, `∏ p_i ≤ F_k(√(12/5^{15/16}))` (39); if `18 ≤ p_1 < 258`,
`∏ p_i ≤ F_k(√(512/255^{31/32}))` (40); if `p_1 ≥ 258`,
`∏ p_i ≤ F_k(√(2^{5/4} (2^{16} + 1)/2^{16}))` (41).

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 7. -/
public theorem_wanted hbcAdmissible_half_prime_prod_le_of_five_le (k : ℕ) (y : ℕ → ℕ) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hprime : ∀ i ∈ Finset.Icc 1 k, (y i).Prime)
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (h5 : 5 ≤ y 1) :
    let F : ℝ → ℝ := fun x => x ^ 2 ^ k - x ^ 2 ^ (k - 1)
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (8 / (3 : ℝ) ^ ((7 : ℝ) / 8))) ∧
      (6 ≤ y 1 → y 1 < 18 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (12 / (5 : ℝ) ^ ((15 : ℝ) / 16)))) ∧
      (18 ≤ y 1 → y 1 < 258 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤ F (Real.sqrt (512 / (255 : ℝ) ^ ((31 : ℝ) / 32)))) ∧
      (258 ≤ y 1 →
        ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
          F (Real.sqrt ((2 : ℝ) ^ ((5 : ℝ) / 4) * (2 ^ 16 + 1) / 2 ^ 16)))

/-- Let `p_1 < ⋯ < p_k` be primes with `∏_{i=1}^k (1 - 1/p_i) ≤ 1/2 < ∏_{i=1}^{k-1} (1 - 1/p_i)`
(51) and `p_1 = 5`. Then `∏_{i=1}^k p_i ≤ F_k(√(8/3^{31/32}))` (52), where
`F_k(x) = x^{2^k} - x^{2^{k-1}}`.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 8. -/
public theorem_wanted hbcAdmissible_half_prime_prod_le_of_eq_five (k : ℕ) (y : ℕ → ℕ) (hmono : ∀ i, 1 ≤ i → i < k → y i < y (i + 1))
    (hprime : ∀ i ∈ Finset.Icc 1 k, (y i).Prime)
    (hle : ∏ i ∈ Finset.Icc 1 k, (1 - 1 / (y i : ℝ)) ≤ 1 / 2)
    (hlt : 1 / 2 < ∏ i ∈ Finset.Icc 1 (k - 1), (1 - 1 / (y i : ℝ)))
    (h5 : y 1 = 5) :
    ∏ i ∈ Finset.Icc 1 k, (y i : ℝ) ≤
      Real.sqrt (8 / (3 : ℝ) ^ ((31 : ℝ) / 32)) ^ 2 ^ k -
        Real.sqrt (8 / (3 : ℝ) ^ ((31 : ℝ) / 32)) ^ 2 ^ (k - 1)

end

end MetaMathlibExt
