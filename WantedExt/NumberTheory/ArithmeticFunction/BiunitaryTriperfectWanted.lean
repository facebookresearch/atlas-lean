/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Rat.Defs
public import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne
public import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowSubOne
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryFortyOne
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisorParity
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectFactorizationTwoNeSixOfBiunitaryTriperfect
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectNotFiveDvdOfFactorizationTwoEqFour
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectExistsPrimeGeFiveDvdSigmaBiunitaryPrimePow
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectEq2160OfFactorizationTwoEqFour

/-!
# Biunitary triperfect numbers divisible by `27`

Statements from Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain
Form*, Journal of Integer Sequences 28 (2025), Article 25.4.5.
`MetaMathlibExt.four_le_factorization_two_of_biunitaryTriperfect` is in
`MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect`.

Following Wall (as quoted in the paper's introduction), a divisor `d` of `n` is biunitary when
`gcd₁(d, n / d) = 1`, where `gcd₁(a, b)` is the greatest common unitary divisor of `a` and `b`
(a unitary divisor of `a` is a divisor `d` with `gcd(d, a / d) = 1`, `Nat.unitaryDivisors`).
The paper's `σ**(n)` is `MetaMathlibExt.sigmaBiunitary n` (with `gcd₁` and the biunitary
divisors in `MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor`), and `ω(n)` is
`n.primeFactors.card`.
Exponents are written with `Nat.factorization`: `2 ^ e ∥ N` is `N.factorization 2 = e`.

Lemmas 2.3 and 2.4 (Bang–Zsigmondy) use `IntegerSequence.IsPrimitivePrimeDivisor`, whose
earlier indices are `1 ≤ m < n`. The existence half of Lemma 2.3 is already proved as
`MetaMathlibExt.bangZsigmondy_exists_primitivePrimeDivisor` (with `b = 1`), so only its
congruence half is stated here.

Lemma 2.7 (III) (two distinct prime factors `≥ 127` of `σ**(3^f)` for `f ≥ 18` or
`f ∈ {13, 14}`) is not stated: it is false as printed for `f = 19, 20, 23, 24`, e.g.
`σ**(3^19) = 1743392200 = 2³ · 5² · 11² · 61 · 1181`. The paper's proofs of Theorem 1.1 and
Lemma 3.7 invoke it, so those statements are recorded as claimed, not as checked proofs.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The only biunitary triperfect number divisible by $27$ is $2160$.** For every positive
integer $N$ divisible by $27$, $\sigma^{**}(N) = 3N$ if and only if $N = 2160$, where
$\sigma^{**}$ is the biunitary divisor sum.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Theorem 1 (`jis-2025-25.4.5-thm-1`). -/
public theorem_wanted sigmaBiunitary_eq_three_mul_iff_of_twentySeven_dvd (N : ℕ) (hN : 0 < N)
    (h27 : 27 ∣ N) : sigmaBiunitary N = 3 * N ↔ N = 2160

/-- **Divisibility of the biunitary divisor sum of an even number by a power of two.** For every
positive even natural number $n$, writing $\omega(n)$ for the number of distinct prime factors of
$n$, the power $2^{\omega(n) - 1}$ divides the biunitary divisor sum $\sigma^{**}(n)$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem_wanted two_pow_card_primeFactors_sub_one_dvd_sigmaBiunitary_of_even (n : ℕ)
    (hn : 0 < n) (he : Even n) : 2 ^ (n.primeFactors.card - 1) ∣ sigmaBiunitary n

/-- **Prime factors of the biunitary divisor sum of a power of $3$.** Let $f$, $t$ and $\eta$ be
natural numbers with $\eta \in \{0, 1\}$ and $f = 2t - 1 - \eta$, suppose $f \ge 5$, and write
$\sigma^{**}$ for the biunitary divisor sum. Then at least one of the following holds:
(A) $\eta = 0$ and $\sigma^{**}(3^f)$ has a prime factor $p$ with $5 < p \le (3^t - 1)/2$;
(B) $5 \mid \sigma^{**}(3^f)$, and $f \equiv 2 \pmod 4$ or $f \in \{7, 8\}$;
(C) $\sigma^{**}(3^f)$ has a prime factor $p$ with $p > 5$ and $p^2 \le (3^{t - \eta} - 1)/2$;
(D) $4 \mid t$, $\eta = 1$, and $(3^{t-1} - 1)/2$ is prime.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 6 (`jis-2025-25.4.5-lem-6`). -/
public theorem_wanted sigmaBiunitary_three_pow_cases (f t η : ℕ) (hη : η ≤ 1)
    (hft : f + 1 + η = 2 * t) (hf : 5 ≤ f) :
    (η = 0 ∧ ∃ p, p.Prime ∧ p ∣ sigmaBiunitary (3 ^ f) ∧ 5 < p ∧ p ≤ (3 ^ t - 1) / 2) ∨
      (5 ∣ sigmaBiunitary (3 ^ f) ∧ (f % 4 = 2 ∨ f = 7 ∨ f = 8)) ∨
      (∃ p, p.Prime ∧ p ∣ sigmaBiunitary (3 ^ f) ∧ 5 < p ∧ p ^ 2 ≤ (3 ^ (t - η) - 1) / 2) ∨
      (4 ∣ t ∧ η = 1 ∧ ((3 ^ (t - 1) - 1) / 2).Prime)

/-- **Prime factors of the biunitary divisor sum of a power of $2$.** Let $e$, $s$ and $\delta$
be natural numbers with $\delta \in \{0, 1\}$ and $e = 2s - 1 - \delta$, suppose $e \ge 6$ and
$e \notin \{8, 12\}$, and write $\sigma^{**}$ for the biunitary divisor sum. Then at least one of
the following holds:
(a) $\delta = 0$ and $\sigma^{**}(2^e)$ has two distinct prime factors $q_1, q_2$ with
$5 < q_i \le 2^s - 1$ for $i = 1, 2$;
(b) $5 \mid \sigma^{**}(2^e)$;
(c) $\sigma^{**}(2^e)$ has two distinct prime factors $q_1, q_2$ such that each $q_i$ equals
$2^{s-1} - 1$ or $2^s + 1$ or satisfies $5 < q_i$ and $q_i^2 \le 2^s - 3$, and if some $q_i$
equals $2^{s-1} - 1$ or $2^s + 1$, then $4 \mid s$ and $\delta = 1$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 7 (`jis-2025-25.4.5-lem-7`). -/
public theorem_wanted sigmaBiunitary_two_pow_cases (e s δ : ℕ) (hδ : δ ≤ 1)
    (hes : e + 1 + δ = 2 * s) (he : 6 ≤ e) (he8 : e ≠ 8) (he12 : e ≠ 12) :
    (δ = 0 ∧ ∃ q₁ q₂, q₁ ≠ q₂ ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ∣ sigmaBiunitary (2 ^ e) ∧
        q₂ ∣ sigmaBiunitary (2 ^ e) ∧ 5 < q₁ ∧ q₁ ≤ 2 ^ s - 1 ∧ 5 < q₂ ∧ q₂ ≤ 2 ^ s - 1) ∨
      5 ∣ sigmaBiunitary (2 ^ e) ∨
      (∃ q₁ q₂, q₁ ≠ q₂ ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ∣ sigmaBiunitary (2 ^ e) ∧
        q₂ ∣ sigmaBiunitary (2 ^ e) ∧
        ∀ q ∈ ({q₁, q₂} : Finset ℕ),
          (q = 2 ^ (s - 1) - 1 ∨ q = 2 ^ s + 1 ∨ (5 < q ∧ q ^ 2 ≤ 2 ^ s - 3)) ∧
            ((q = 2 ^ (s - 1) - 1 ∨ q = 2 ^ s + 1) → 4 ∣ s ∧ δ = 1))

/-- **Prime factors at least $7$ of biunitary divisor sums of odd prime powers.** For every odd
prime $p$ and every integer $g \ge 4$, the biunitary divisor sum $\sigma^{**}(p^g)$ has a prime
factor $q \ge 7$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (II) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow (p g : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2) (hg : 4 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 7 ≤ q

/-- **Two prime factors of the biunitary divisor sum of $13^g$.** For every integer $g \ge 2$, the
biunitary divisor sum $\sigma^{**}(13^g)$ has two distinct prime factors $q_1$ and $q_2$, neither
of which lies in $\{2, 3, 41, 547\}$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (IV) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_two_primes_dvd_sigmaBiunitary_thirteen_pow (g : ℕ) (hg : 2 ≤ g) :
    ∃ q₁ q₂, q₁ ≠ q₂ ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ∣ sigmaBiunitary (13 ^ g) ∧
      q₂ ∣ sigmaBiunitary (13 ^ g) ∧ q₁ ∉ ({2, 3, 41, 547} : Finset ℕ) ∧
      q₂ ∉ ({2, 3, 41, 547} : Finset ℕ)

/-- **No biunitary triperfect number divisible by $27$ is exactly divisible by $2^5$.** Let $N$
be a biunitary triperfect number, that is, a positive integer with $\sigma^{**}(N) = 3N$, where
$\sigma^{**}$ is the biunitary divisor sum. If $3^3$ divides $N$, then the exact power of $2$
dividing $N$ is not $2^5$.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 10 (`jis-2025-25.4.5-lem-10`). -/
public theorem_wanted factorization_two_ne_five_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    N.factorization 2 ≠ 5

/-- **No biunitary triperfect number has $3$-exponent $3$ and $2$-exponent at least $7$.** Let
$N$ be a positive integer with $\sigma^{**}(N) = 3N$, where $\sigma^{**}$ is the biunitary divisor
sum, and let $e$ and $f$ be the exponents of $2$ and $3$ in the prime factorization of $N$. If
$f \ge 3$, then $e \ge 7$ and $f = 3$ do not both hold.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 12 (`jis-2025-25.4.5-lem-12`). -/
public theorem_wanted not_seven_le_and_factorization_three_eq_three (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    ¬ (7 ≤ N.factorization 2 ∧ N.factorization 3 = 3)

/-- **No biunitary triperfect number has $3$-exponent $4$ and $2$-exponent at least $7$.** Let
$N$ be a positive integer with $\sigma^{**}(N) = 3N$, where $\sigma^{**}$ is the biunitary divisor
sum, and let $e$ and $f$ be the exponents of $2$ and $3$ in the prime factorization of $N$. If
$f \ge 3$, then $e \ge 7$ and $f = 4$ do not both hold.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 13 (`jis-2025-25.4.5-lem-13`). -/
public theorem_wanted not_seven_le_and_factorization_three_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    ¬ (7 ≤ N.factorization 2 ∧ N.factorization 3 = 4)

end

end MetaMathlibExt
