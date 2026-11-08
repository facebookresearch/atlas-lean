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
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor

/-!
# Biunitary triperfect numbers divisible by `27`

Statements from Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain
Form*, Journal of Integer Sequences 28 (2025), Article 25.4.5.

Following Wall (as quoted in the paper's introduction), a divisor `d` of `n` is biunitary when
`gcd₁(d, n / d) = 1`, where `gcd₁(a, b)` is the greatest common unitary divisor of `a` and `b`
(a unitary divisor of `a` is a divisor `d` with `gcd(d, a / d) = 1`, `Nat.unitaryDivisors`).
The paper's `σ**(n)` is `MetaMathlibExt.sigmaBiunitary n` (with `gcd₁` and the biunitary
divisors in `MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryDivisor`), and `ω(n)` is `n.primeFactors.card`.
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

/-- There is exactly one biunitary triperfect number divisible by `3³`, namely `2160`:
for positive `N` with `27 ∣ N`, `σ**(N) = 3N` iff `N = 2160`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Theorem 1 (`jis-2025-25.4.5-thm-1`). -/
public theorem_wanted sigmaBiunitary_eq_three_mul_iff_of_twentySeven_dvd (N : ℕ) (hN : 0 < N)
    (h27 : 27 ∣ N) : sigmaBiunitary N = 3 * N ↔ N = 2160

/-- For positive `n`, `σ**(n)` is odd iff `n` is a power of `2` (including `1`).

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem_wanted odd_sigmaBiunitary_iff (n : ℕ) (hn : 0 < n) :
    Odd (sigmaBiunitary n) ↔ ∃ k : ℕ, n = 2 ^ k

/-- For odd `n`, `2 ^ ω(n)` divides `σ**(n)`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem_wanted two_pow_card_primeFactors_dvd_sigmaBiunitary_of_odd (n : ℕ)
    (hn : Odd n) : 2 ^ n.primeFactors.card ∣ sigmaBiunitary n

/-- For positive even `n`, `2 ^ (ω(n) - 1)` divides `σ**(n)`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 2 (`jis-2025-25.4.5-lem-2`). -/
public theorem_wanted two_pow_card_primeFactors_sub_one_dvd_sigmaBiunitary_of_even (n : ℕ)
    (hn : 0 < n) (he : Even n) : 2 ^ (n.primeFactors.card - 1) ∣ sigmaBiunitary n

/-- Lower bounds for `σ**(p^e) / p^e` (in `ℚ`) for a prime `p` and `e ≥ 1`: it is at least
`1 + 1/p²`; at least `1 + 1/p` unless `e = 2`; at least `(1 + 1/p)(1 + 1/p³)` if `e ≥ 3`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3 (`jis-2025-25.4.5-lem-3`). -/
public theorem_wanted sigmaBiunitary_prime_pow_div_ge (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    (1 + 1 / (p : ℚ) ^ 2 ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (e ≠ 2 → 1 + 1 / (p : ℚ) ≤ (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (3 ≤ e → (1 + 1 / (p : ℚ)) * (1 + 1 / (p : ℚ) ^ 3) ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e)

/-- For a prime `p` and positive integers `m`, `e` with `e ≥ 2m - 1`,
`σ**(p^e) / p^e ≥ σ**(p^{2m}) / p^{2m}`, and, unless `e = 2m`,
`σ**(p^e) / p^e ≥ 1 + 1/p + ⋯ + 1/p^m` (in `ℚ`).

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 3 (`jis-2025-25.4.5-lem-3`). -/
public theorem_wanted sigmaBiunitary_prime_pow_div_ge_of_two_mul_sub_one_le (p m e : ℕ)
    (hp : p.Prime) (hm : 0 < m) (he : 2 * m - 1 ≤ e) :
    ((sigmaBiunitary (p ^ (2 * m)) : ℚ) / (p : ℚ) ^ (2 * m) ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e) ∧
      (e ≠ 2 * m → ∑ i ∈ Finset.range (m + 1), 1 / (p : ℚ) ^ i ≤
        (sigmaBiunitary (p ^ e) : ℚ) / (p : ℚ) ^ e)

/-- Bang's theorem, congruence half: for integers `a ≥ 2`, `n ≥ 2`, every prime factor of
`a^n - 1` dividing no `a^m - 1` with `1 ≤ m < n` is `≡ 1 (mod n)`. The existence half (a
primitive prime factor exists unless `(a, n) = (2, 6)` or `n = 2` and `a + 1` is a power of
`2`) is `MetaMathlibExt.bangZsigmondy_exists_primitivePrimeDivisor` with `b = 1`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 4 (`jis-2025-25.4.5-lem-4`),
quoting Bang. -/
public theorem_wanted primitivePrimeDivisor_pow_sub_one_mod_eq_one (a n p : ℕ) (ha : 2 ≤ a)
    (hn : 2 ≤ n)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - 1) n p) :
    p % n = 1

/-- For integers `a ≥ 2`, `n ≥ 1`, `a^n + 1` has a prime factor dividing no `a^m + 1` with
`1 ≤ m < n` and congruent to `1` modulo `2n`, unless `(a, n) = (2, 3)` or `n = 1` and `a + 1`
is a power of `2`. The second exception is not in the printed statement: for `a = 3`, `n = 1`
the only prime factor of `3 + 1 = 4` is `2 ≢ 1 (mod 2)`; the paper's proof applies Lemma 2.3 to
`a^{2n} - 1`, whose exceptions include exactly this case.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 5 (`jis-2025-25.4.5-lem-5`). -/
public theorem_wanted exists_primitivePrimeDivisor_pow_add_one (a n : ℕ) (ha : 2 ≤ a)
    (hn : 1 ≤ n) (hexc : ¬ (a = 2 ∧ n = 3)) (hexc' : ¬ (n = 1 ∧ ∃ k : ℕ, a + 1 = 2 ^ k)) :
    ∃ p, IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m + 1) n p ∧
      p % (2 * n) = 1

/-- Write `f = 2t - 1 - η` with `η ∈ {0, 1}`. If `f ≥ 5`, then at least one of:
(A) `η = 0` and `σ**(3^f)` has a prime factor `p₁` with `5 < p₁ ≤ (3^t - 1)/2`;
(B) `5 ∣ σ**(3^f)` and (`f ≡ 2 (mod 4)` or `f ∈ {7, 8}`);
(C) `σ**(3^f)` has a prime factor `p₁` with `5 < p₁ ≤ √((3^{t-η} - 1)/2)` (as `p₁² ≤ ⋯`);
(D) `4 ∣ t`, `η = 1`, and `(3^{t-1} - 1)/2` is prime.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 6 (`jis-2025-25.4.5-lem-6`). -/
public theorem_wanted sigmaBiunitary_three_pow_cases (f t η : ℕ) (hη : η ≤ 1)
    (hft : f + 1 + η = 2 * t) (hf : 5 ≤ f) :
    (η = 0 ∧ ∃ p, p.Prime ∧ p ∣ sigmaBiunitary (3 ^ f) ∧ 5 < p ∧ p ≤ (3 ^ t - 1) / 2) ∨
      (5 ∣ sigmaBiunitary (3 ^ f) ∧ (f % 4 = 2 ∨ f = 7 ∨ f = 8)) ∨
      (∃ p, p.Prime ∧ p ∣ sigmaBiunitary (3 ^ f) ∧ 5 < p ∧ p ^ 2 ≤ (3 ^ (t - η) - 1) / 2) ∨
      (4 ∣ t ∧ η = 1 ∧ ((3 ^ (t - 1) - 1) / 2).Prime)

/-- Write `e = 2s - 1 - δ` with `δ ∈ {0, 1}`. If `e ≥ 6` and `e ≠ 8, 12`, then at least one of:
(a) `δ = 0` and `σ**(2^e)` has two distinct prime factors `q₁, q₂` with `5 < qᵢ ≤ 2^s - 1`;
(b) `5 ∣ σ**(2^e)`;
(c) `σ**(2^e)` has two distinct prime factors `q₁, q₂`, each equal to `2^{s-1} - 1` or `2^s + 1`
or with `5 < qᵢ ≤ √(2^s - 3)` (as `qᵢ² ≤ 2^s - 3`), and `4 ∣ s ∧ δ = 1` whenever some `qᵢ`
equals `2^{s-1} - 1` or `2^s + 1`.

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

/-- For a prime `p` and `g ≥ 2`, `σ**(p^g)` has a prime factor `≥ 5`, except for
`(p, g) = (2, 4)`. The exception is not in the printed statement: `σ**(2⁴) = 27 = 3³`; the
paper's proof applies Lemma 2.4 to `p^u + 1` with `g = 2u - 1 - ε`, and `(p, u) = (2, 3)` is
that lemma's exception.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (I) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_prime_ge_five_dvd_sigmaBiunitary_prime_pow (p g : ℕ)
    (hp : p.Prime) (hg : 2 ≤ g) (hexc : ¬ (p = 2 ∧ g = 4)) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 5 ≤ q

/-- For an odd prime `p` and `g ≥ 4`, `σ**(p^g)` has a prime factor `≥ 7`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (II) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow (p g : ℕ)
    (hp : p.Prime) (hodd : p ≠ 2) (hg : 4 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (p ^ g) ∧ 7 ≤ q

/-- If `g ≥ 2`, then `σ**(13^g)` has two distinct prime factors outside `{2, 3, 41, 547}`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (IV) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_two_primes_dvd_sigmaBiunitary_thirteen_pow (g : ℕ) (hg : 2 ≤ g) :
    ∃ q₁ q₂, q₁ ≠ q₂ ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ∣ sigmaBiunitary (13 ^ g) ∧
      q₂ ∣ sigmaBiunitary (13 ^ g) ∧ q₁ ∉ ({2, 3, 41, 547} : Finset ℕ) ∧
      q₂ ∉ ({2, 3, 41, 547} : Finset ℕ)

/-- For `g ≥ 1`, `σ**(41^g)` has a prime factor outside `{2, 3, 5, 13}`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 8 (V) (`jis-2025-25.4.5-lem-8`). -/
public theorem_wanted exists_prime_dvd_sigmaBiunitary_fortyOne_pow (g : ℕ) (hg : 1 ≤ g) :
    ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (41 ^ g) ∧ q ∉ ({2, 3, 5, 13} : Finset ℕ)

/-- Section 3 setting: `N` is biunitary triperfect with `2^e ∥ N`, `3^f ∥ N`, `f ≥ 3`. Then
`e ≥ 4`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 9 (`jis-2025-25.4.5-lem-9`). -/
public theorem_wanted four_le_factorization_two_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    4 ≤ N.factorization 2

/-- Section 3 setting (`N` biunitary triperfect, `3^f ∥ N`, `f ≥ 3`): `2^5 ∥ N` is impossible.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 10 (`jis-2025-25.4.5-lem-10`). -/
public theorem_wanted factorization_two_ne_five_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    N.factorization 2 ≠ 5

/-- Section 3 setting (`N` biunitary triperfect, `3^f ∥ N`, `f ≥ 3`): `2^6 ∥ N` is impossible.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 11 (`jis-2025-25.4.5-lem-11`). -/
public theorem_wanted factorization_two_ne_six_of_biunitaryTriperfect (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    N.factorization 2 ≠ 6

/-- Section 3 setting (`N` biunitary triperfect, `2^e ∥ N`, `3^f ∥ N`, `f ≥ 3`): `e ≥ 7` and
`f = 3` cannot both hold.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 12 (`jis-2025-25.4.5-lem-12`). -/
public theorem_wanted not_seven_le_and_factorization_three_eq_three (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    ¬ (7 ≤ N.factorization 2 ∧ N.factorization 3 = 3)

/-- Section 3 setting (`N` biunitary triperfect, `2^e ∥ N`, `3^f ∥ N`, `f ≥ 3`): `e ≥ 7` and
`f = 4` cannot both hold.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 13 (`jis-2025-25.4.5-lem-13`). -/
public theorem_wanted not_seven_le_and_factorization_three_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3) :
    ¬ (7 ≤ N.factorization 2 ∧ N.factorization 3 = 4)

/-- Section 3 setting (`N` biunitary triperfect, `2^e ∥ N`, `3^f ∥ N`, `f ≥ 3`): if `e = 4`
and `f ≤ 4`, then `N = 2160`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 14 (`jis-2025-25.4.5-lem-14`). -/
public theorem_wanted eq_2160_of_factorization_two_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (hf : 3 ≤ N.factorization 3)
    (he : N.factorization 2 = 4) (hf4 : N.factorization 3 ≤ 4) : N = 2160

/-- Section 3 setting (`N` biunitary triperfect, `2^e ∥ N`, `3^f ∥ N`, `f ≥ 3`): if `e = 4`
and `f ≥ 5`, then `5 ∤ N`.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 15 (`jis-2025-25.4.5-lem-15`). -/
public theorem_wanted not_five_dvd_of_factorization_two_eq_four (N : ℕ) (hN : 0 < N)
    (hσ : sigmaBiunitary N = 3 * N) (he : N.factorization 2 = 4)
    (hf5 : 5 ≤ N.factorization 3) : ¬ 5 ∣ N

end

end MetaMathlibExt
