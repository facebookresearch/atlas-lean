/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.EulerPrime
public import WantedExt.NumberTheory.PrimitiveNondeficientWanted

/-! # Prime reciprocal sums of odd perfect and primitive non-deficient numbers

Statement-only requests from Joshua Zelinsky, *The Sum of the Reciprocals of the Prime
Divisors of an Odd Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025),
Article A59 (arXiv:2402.14234v5). The paper writes `T(n) = ∑_{p ∣ n} 1/p`, spelled out
below as `∑ p ∈ n.primeFactors, (1 : ℝ) / p`; `H(n) = ∏_{p ∣ n} p/(p-1)` is
`abundancySup`, `h(n) = σ(n)/n` is `abundancyIndex`, and the surplus of a non-deficient
`n` is `S(n) = H(n) - 2`. Non-deficient and primitive non-deficient are
`IsNondeficient` and `IsPrimitiveNondeficient`; the paper's least prime factor `p₁` is
`n.minFac`. An odd perfect number is `Odd n ∧ n.Perfect`, and Euler's form with special
prime `q` is `EulerianForm`.
-/

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

namespace MetaMathlibExt

@[expose] public section

/-- If `n` is an odd perfect number with least prime factor `p₁ ≥ 11`, then
`T(n) < log 2 - 11/(50 p₁²)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Corollary 1 (`integers-2025-A59-cor-1`). -/
public theorem_wanted oddPerfect_primeReciprocalSum_lt_log_two_sub
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h11 : 11 ≤ n.minFac) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / p < Real.log 2 - 11 / (50 * (n.minFac : ℝ) ^ 2)

/-- If `n` is an odd perfect number with least prime factor `p₁ ≥ 11`, then its surplus
satisfies `S(n) = H(n) - 2 < 25/(8 p₁ log p₁)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Corollary 2 (`integers-2025-A59-cor-2`). -/
public theorem_wanted oddPerfect_abundancySup_sub_two_lt
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h11 : 11 ≤ n.minFac) :
    (abundancySup n : ℝ) - 2 < 25 / (8 * (n.minFac : ℝ) * Real.log n.minFac)

/-- For `0 ≤ x ≤ 1/11`, `1 + x + x² ≥ exp(x + 2x²/5)`, with equality exactly at `x = 0`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 3 (`integers-2025-A59-lem-3`). -/
public theorem_wanted exp_add_two_fifths_sq_le_one_add_add_sq
    (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 11) :
    Real.exp (x + 2 * x ^ 2 / 5) ≤ 1 + x + x ^ 2 ∧
      (Real.exp (x + 2 * x ^ 2 / 5) = 1 + x + x ^ 2 ↔ x = 0)

/-- For every prime `p ≥ 19`, `π(p) ≥ p / log p + 1`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 4 (`integers-2025-A59-lem-4`). -/
public theorem_wanted div_log_add_one_le_primeCounting
    (p : ℕ) (hp : p.Prime) (h19 : 19 ≤ p) :
    (p : ℝ) / Real.log p + 1 ≤ Nat.primeCounting p

/-- For a prime `q ≥ 3`, `M(q) = ∑_{p ≥ q} 1/p²` over primes `p` satisfies
`M(q) < (1/(q log q)) (1 + 2 log log q / log q)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 6 (`integers-2025-A59-lem-6`). -/
public theorem_wanted tsum_one_div_sq_primes_ge_lt
    (q : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) :
    ∑' p : {p : ℕ // p.Prime ∧ q ≤ p}, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 <
      1 / ((q : ℝ) * Real.log q) * (1 + 2 * Real.log (Real.log q) / Real.log q)

/-- For an odd prime `q`, `E = ∏_{p ≥ q} p²/(p²-1)` over primes `p` satisfies
`log E ≤ (1/(q log q)) (1 + 2 log log q / log q) + 4/q³`. The infinite product is
stated through its logarithm, `log E = ∑_{p ≥ q} log (p²/(p²-1))`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 7 (`integers-2025-A59-lem-7`). -/
public theorem_wanted tsum_log_sq_div_sq_sub_one_primes_ge_le
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) :
    ∑' p : {p : ℕ // p.Prime ∧ q ≤ p},
        Real.log (((p : ℕ) : ℝ) ^ 2 / (((p : ℕ) : ℝ) ^ 2 - 1)) ≤
      1 / ((q : ℝ) * Real.log q) * (1 + 2 * Real.log (Real.log q) / Real.log q) +
        4 / (q : ℝ) ^ 3

/-- For an integer `x ≥ 2`, `log(1 + 1/(x-1)) ≤ 1/x + 25/(32 x²)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 8 (`integers-2025-A59-lem-8`). -/
public theorem_wanted log_one_add_one_div_sub_one_le
    (x : ℕ) (hx : 2 ≤ x) :
    Real.log (1 + 1 / ((x : ℝ) - 1)) ≤ 1 / (x : ℝ) + 25 / (32 * (x : ℝ) ^ 2)

/-- (Suryanarayana) Let `n` be odd with every prime exponent even except the exponent of
a single prime `p_j`, which is odd. Then
`H(n)/h(n) ≤ p_j²/(p_j²-1) · ∏_{i ≠ j} p_i³/(p_i³-1)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 9 (`integers-2025-A59-lem-9`). -/
public theorem_wanted abundancySup_div_abundancyIndex_le_of_single_odd_exponent
    (n j : ℕ) (hn : Odd n) (hj : j ∈ n.primeFactors) (hjodd : Odd (n.factorization j))
    (heven : ∀ p ∈ n.primeFactors, p ≠ j → Even (n.factorization p)) :
    abundancySup n / abundancyIndex n ≤
      (j : ℚ) ^ 2 / ((j : ℚ) ^ 2 - 1) *
        ∏ p ∈ n.primeFactors.erase j, (p : ℚ) ^ 3 / ((p : ℚ) ^ 3 - 1)

/-- If `n` is an odd perfect number divisible by `165`, then `5` divides `n` exactly once.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 11 (`integers-2025-A59-lem-11`). -/
public theorem_wanted oddPerfect_factorization_five_eq_one_of_dvd
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h165 : 165 ∣ n) :
    n.factorization 5 = 1

/-- If `p₁, …, p_m` are distinct odd primes with `∏ pᵢ/(pᵢ-1) ≤ 2`, and `q` is an odd
prime with `(∏ pᵢ/(pᵢ-1)) · q/(q-1) > 2`, then `q ≤ 2 ∏ (pᵢ - 1) - 1`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 12 (`integers-2025-A59-lem-12`). -/
public theorem_wanted le_two_mul_prod_sub_one_sub_one_of_two_lt
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ Odd p)
    (hle : ∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1) ≤ 2)
    (q : ℕ) (hq : q.Prime) (hqodd : Odd q)
    (hgt : 2 < (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) * ((q : ℚ) / ((q : ℚ) - 1))) :
    q ≤ 2 * ∏ p ∈ s, (p - 1) - 1

/-- (Cohen, Hagis, Suryanarayana) Upper bounds for `T(n)` for an odd perfect number `n`,
by `gcd(15, n)`: `0.693148` for `1`, `0.657304` for `3`, `0.678036` for `5`, and
`0.673770` for `15`. The table's lower bounds are omitted.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 1, Table 1 (`integers-2025-A59-prop-1`). -/
public theorem_wanted oddPerfect_primeReciprocalSum_le_of_gcd_fifteen
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    (Nat.gcd 15 n = 1 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.693148) ∧
      (Nat.gcd 15 n = 3 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.657304) ∧
      (Nat.gcd 15 n = 5 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.678036) ∧
      (Nat.gcd 15 n = 15 → ∑ p ∈ n.primeFactors, (1 : ℝ) / p ≤ 0.673770)

/-- (Suryanarayana) Upper bounds for `H(n)` for an odd perfect number `n`, by
`gcd(15, n)`: `2.014754` for `1`, `2.096234` for `3`, `2.031002` for `5`, and `2.165439`
for `15`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 2, Table 2 (`integers-2025-A59-prop-2`). -/
public theorem_wanted oddPerfect_abundancySup_le_of_gcd_fifteen
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    (Nat.gcd 15 n = 1 → abundancySup n ≤ 2.014754) ∧
      (Nat.gcd 15 n = 3 → abundancySup n ≤ 2.096234) ∧
      (Nat.gcd 15 n = 5 → abundancySup n ≤ 2.031002) ∧
      (Nat.gcd 15 n = 15 → abundancySup n ≤ 2.165439)

/-- If `n` is primitive non-deficient with least prime factor `p₁` and surplus
`S = H(n) - 2`, then `T(n) ≥ log 2 - 25/(64 p₁) + S/2 - S²/4`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 3 (`integers-2025-A59-prop-3`). -/
public theorem_wanted primitiveNondeficient_primeReciprocalSum_ge
    (n : ℕ) (hn : IsPrimitiveNondeficient n) :
    Real.log 2 - 25 / (64 * (n.minFac : ℝ)) + ((abundancySup n : ℝ) - 2) / 2 -
        ((abundancySup n : ℝ) - 2) ^ 2 / 4 ≤
      ∑ p ∈ n.primeFactors, (1 : ℝ) / p

/-- Let `n` be primitive non-deficient whose prime exponents are all even except that of
one prime `p_t`, which is odd, and assume `(p_t + 2)/2 ≥ p₁ ≥ 11`. Then
`T(n) < log 2 - 11/(50 p₁²)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 4 (`integers-2025-A59-prop-4`). -/
public theorem_wanted primitiveNondeficient_primeReciprocalSum_lt_of_single_odd_exponent
    (n t : ℕ) (hn : IsPrimitiveNondeficient n) (ht : t ∈ n.primeFactors)
    (htodd : Odd (n.factorization t))
    (heven : ∀ p ∈ n.primeFactors, p ≠ t → Even (n.factorization p))
    (h11 : 11 ≤ n.minFac) (hpt : 2 * n.minFac ≤ t + 2) :
    ∑ p ∈ n.primeFactors, (1 : ℝ) / p < Real.log 2 - 11 / (50 * (n.minFac : ℝ) ^ 2)

/-- If `n` is an odd perfect number with least prime factor `p₁`, then
`H(n) ≤ 2 + 9/(4 p₁²)`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 5 (`integers-2025-A59-prop-5`). -/
public theorem_wanted oddPerfect_abundancySup_le
    (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) :
    abundancySup n ≤ 2 + 9 / (4 * (n.minFac : ℚ) ^ 2)

/-- If `n` is an odd primitive non-deficient number with least prime factor `p₁` and
surplus `S = H(n) - 2`, then
`T(n) ≥ log 2 - (25/(32 p₁ log p₁)) (1 + 2 log log p₁ / log p₁) + S/2 - S²/4`.
The hypothesis `Odd n` is added: the printed statement fails at `n = 6`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 7 (`integers-2025-A59-prop-7`). -/
public theorem_wanted odd_primitiveNondeficient_primeReciprocalSum_ge
    (n : ℕ) (hodd : Odd n) (hn : IsPrimitiveNondeficient n) :
    Real.log 2 -
          25 / (32 * (n.minFac : ℝ) * Real.log n.minFac) *
            (1 + 2 * Real.log (Real.log n.minFac) / Real.log n.minFac) +
        ((abundancySup n : ℝ) - 2) / 2 - ((abundancySup n : ℝ) - 2) ^ 2 / 4 ≤
      ∑ p ∈ n.primeFactors, (1 : ℝ) / p

/-- There is a constant `C` such that every primitive non-deficient `n` with least prime
factor `p₁` satisfies `H(n) ≤ 2 + C/p₁`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 8 (`integers-2025-A59-prop-8`). -/
public theorem_wanted exists_abundancySup_le_two_add_div_minFac :
    ∃ C : ℝ, ∀ n : ℕ, IsPrimitiveNondeficient n →
      (abundancySup n : ℝ) ≤ 2 + C / n.minFac

/-- A prime `q ≡ -1 (mod 165)` is not the special (Euler) prime of any odd perfect
number.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 9 (`integers-2025-A59-prop-9`). -/
public theorem_wanted not_isEulerPrime_of_mod_165_eq
    (n q : ℕ) (hq : q % 165 = 164) :
    ¬ IsEulerPrime n q

/-- There is no odd prime `q` with `H(odd(q+1)) < 2` and `H(q · odd(q+1)) > 2`, where
`odd(m) = ordCompl[2] m` is the largest odd divisor of `m`. The hypothesis `q` odd is
added: the printed statement fails at `q = 2`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 10 (`integers-2025-A59-prop-10`). -/
public theorem_wanted not_abundancySup_oddPart_succ_lt_two_and_two_lt
    (q : ℕ) (hq : q.Prime) (hodd : Odd q) :
    ¬ (abundancySup (ordCompl[2] (q + 1)) < 2 ∧
      2 < abundancySup (q * ordCompl[2] (q + 1)))

/-- If an odd perfect number has Euler form `n = q^e m²`, then `e = 1` or
`q < 2^{1/5} m^{2/5}`, stated in the equivalent integer form `q⁵ < 2 m²`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 11 (`integers-2025-A59-prop-11`). -/
public theorem_wanted eulerianForm_exponent_eq_one_or_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ q ^ 5 < 2 * m ^ 2

/-- If an odd perfect number has Euler form `n = q^e m²`, then `e = 1` or
`q < (2/((3²)(5²)(11²)(13²)))^{1/5} m^{2/5}`, stated in the equivalent integer form
`3² 5² 11² 13² q⁵ < 2 m²`.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 12 (`integers-2025-A59-prop-12`). -/
public theorem_wanted eulerianForm_exponent_eq_one_or_mul_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ 3 ^ 2 * 5 ^ 2 * 11 ^ 2 * 13 ^ 2 * q ^ 5 < 2 * m ^ 2

end

end MetaMathlibExt
