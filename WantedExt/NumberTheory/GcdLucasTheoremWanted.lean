/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Greatest common divisors of radical-expansion coefficients and Lucas's theorem

Statements from John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2. Write
`(u + v^{1/N})^n = a_{n,0} + a_{n,1} v^{1/N} + ⋯ + a_{n,N-1} v^{(N-1)/N}` with integer
coefficients; the statements below take the coefficient family as a hypothesis-constrained
function, as the paper does, with `v^{1/N}` the real `Real.rpow` root and `v^{i/N}` its
`i`-th power. Lucas's theorem itself is Mathlib's `Choose.choose_modEq_prod_range_choose_nat`;
Corollaries 12 and 13 follow from `Choose.choose_modEq_choose_mod_mul_choose_div_nat` in a few
lines and are not restated.
-/

namespace MetaMathlibExt

@[expose] public section

/-- If `N` has at least two distinct prime factors, `u, v` are coprime positive integers and
`x^N - v` is irreducible over `ℚ`, then for every `n` the integer coefficients of
`(u + v^{1/N})^n` in the basis `1, v^{1/N}, …, v^{(N-1)/N}` exist and are unique.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 3
(`jis-2025-25.2.2-lem-3`). -/
public theorem_wanted existsUnique_radical_expansion_coeffs {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (n : ℕ) :
    ∃! a : Fin N → ℤ, ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ)

/-- Under the hypotheses of Lemma 3, the coefficients `a_{n,0}, …, a_{n,N-1}` of
`(u + v^{1/N})^n` have greatest common divisor `1` for every `n ≥ 1`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 16
(`jis-2025-25.2.2-thm-16`) and its unnumbered restatement in the introduction
(`jis-2025-25.2.2-thm-unnumbered-1`). -/
public theorem_wanted gcd_radical_expansion_coeffs_eq_one {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) = 1

/-- For coprime positive integers `u, v` and `N ≥ 1`,
`gcd(u^N + (-1)^{N+1} v, u) = gcd(u^N + (-1)^{N+1} v, v) = 1`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 5
(`jis-2025-25.2.2-lem-5`). -/
public theorem_wanted gcd_pow_add_neg_one_pow_mul_eq_one {N u v : ℕ} (hN : 1 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v) :
    Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) u = 1 ∧
      Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) v = 1

/-- For a prime `p`, `r > s` and `p ∤ a`, `p ∤ b`, the prime `p` divides `C(p^r a, p^s b)`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 14
(`jis-2025-25.2.2-cor-14`). -/
public theorem_wanted prime_dvd_choose_pow_mul_pow_mul {p a b r s : ℕ} (hp : p.Prime)
    (hrs : s < r) (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : p ∣ (p ^ r * a).choose (p ^ s * b)

/-- For a prime `p`, `r ≥ 1` and `p ∤ a`, `p ∤ b`, `C(p^r a, p^r b) ≡ C(a, b) (mod p)`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 15
(`jis-2025-25.2.2-cor-15`). -/
public theorem_wanted choose_pow_mul_modEq {p a b r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : (p ^ r * a).choose (p ^ r * b) ≡ a.choose b [MOD p]

/-- Let `u, v` be coprime positive integers with `√v` irrational, `(u + √v)^n = a_n + b_n √v`
for `n ≥ 1`, and `D_n = gcd(a_n, b_n)`. (a) If `u² - v` is odd, `D_n = 1`; (b) if
`u² - v ≡ 2 (mod 4)`, `D_{2n-1} = 2^{n-1}` and `D_{2n} = 2^n`; (c) if `u² - v ≡ 4 (mod 8)`,
`D_{3n-2} = 2^{3n-3}`, `D_{3n-1} = 2^{3n-2}`, `D_{3n} = 2^{3n}`; (d) if `u² - v ≡ 0 (mod 8)`,
`D_n = 2^{n-1}`; all for `n ≥ 1`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 17
(`jis-2025-25.2.2-thm-17`). -/
public theorem_wanted gcd_sqrt_expansion_coeffs {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v) (hirr : Irrational (Real.sqrt v)) (a b : ℕ → ℤ)
    (hab : ∀ n, 1 ≤ n → ((u : ℝ) + Real.sqrt v) ^ n = a n + b n * Real.sqrt v) :
    (Odd ((u : ℤ) ^ 2 - v) → ∀ n, 1 ≤ n → Int.gcd (a n) (b n) = 1) ∧
    (((u : ℤ) ^ 2 - v) % 4 = 2 → ∀ n, 1 ≤ n →
      Int.gcd (a (2 * n - 1)) (b (2 * n - 1)) = 2 ^ (n - 1) ∧
        Int.gcd (a (2 * n)) (b (2 * n)) = 2 ^ n) ∧
    (((u : ℤ) ^ 2 - v) % 8 = 4 → ∀ n, 1 ≤ n →
      Int.gcd (a (3 * n - 2)) (b (3 * n - 2)) = 2 ^ (3 * n - 3) ∧
        Int.gcd (a (3 * n - 1)) (b (3 * n - 1)) = 2 ^ (3 * n - 2) ∧
        Int.gcd (a (3 * n)) (b (3 * n)) = 2 ^ (3 * n)) ∧
    (((u : ℤ) ^ 2 - v) % 8 = 0 → ∀ n, 1 ≤ n → Int.gcd (a n) (b n) = 2 ^ (n - 1))

/-- Let `p` be an odd prime, `u, v` coprime positive integers with `v^{1/p}` irrational,
`(u + v^{1/p})^n = ∑_{i<p} a_{n,i} v^{i/p}` for `n ≥ 1`, and `D_n = gcd_i a_{n,i}`.
(a) If `p ∤ u^p + v`, then `D_n = 1` for `n ≥ 1`; (b) if `u^p + v = mp` with `p ∤ m`, then
`D_{np+i} = p^n` for `n ≥ 0`, `0 ≤ i ≤ p - 1` (and `np + i ≥ 1`); (c) if `p² ∣ u^p + v`,
then `D_{n(p-1)+i} = p^n` for `n ≥ 0`, `1 ≤ i ≤ p - 1`.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Theorem 18
(`jis-2025-25.2.2-thm-18`). -/
public theorem_wanted gcd_prime_root_expansion_coeffs {p u v : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v)
    (hirr : Irrational ((v : ℝ) ^ (1 / (p : ℝ)))) (a : ℕ → Fin p → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (p : ℝ))) ^ n =
      ∑ i : Fin p, (a n i : ℝ) * ((v : ℝ) ^ (1 / (p : ℝ))) ^ (i : ℕ)) :
    (¬p ∣ u ^ p + v → ∀ n, 1 ≤ n → Finset.univ.gcd (a n) = 1) ∧
    (∀ m : ℕ, u ^ p + v = m * p → ¬p ∣ m → ∀ n i : ℕ, i ≤ p - 1 → 1 ≤ n * p + i →
      Finset.univ.gcd (a (n * p + i)) = (p : ℤ) ^ n) ∧
    (p ^ 2 ∣ u ^ p + v → ∀ n i : ℕ, 1 ≤ i → i ≤ p - 1 →
      Finset.univ.gcd (a (n * (p - 1) + i)) = (p : ℤ) ^ n)

/-- With `D_n = gcd(a_{n,0}, …, a_{n,N-1})` for the coefficients of `(u + v^{1/N})^n`
(`x^N - v` irreducible over `ℚ`), `D_n ∣ D_{n+1}` for every `n ≥ 1`. The section's standing
`N ≥ 4` and the coprimality of `u, v` are not needed.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 4
(`jis-2025-25.2.2-lem-4`). -/
public theorem_wanted gcd_radical_expansion_coeffs_dvd_succ {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) ∣ Finset.univ.gcd (a (n + 1))

/-- For coprime `u, v`, `N ≥ 2` and `x^N - v` irreducible over `ℚ`, every prime dividing
`gcd(u^N + (-1)^{N+1} v, D_n)` divides `N` (`n ≥ 1`): the gcd is `1` or a product of powers of
primes dividing `N`. The section assumes `N ≥ 4`; `N = 2, 3` also hold (probe, and the paper's
Theorems 17 and 18), while `N = 1` fails (`D_n = (u + v)^n`).

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 6
(`jis-2025-25.2.2-lem-6`). -/
public theorem_wanted prime_dvd_gcd_pow_add_radical_coeffs {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime)
    (hpd : (p : ℤ) ∣ GCDMonoid.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) (Finset.univ.gcd (a n))) :
    p ∣ N

/-- If a prime `p` divides `D_n` for some `n ≥ 1`, then `p ∣ u^N + (-1)^{N+1} v` (the norm of
`u + v^{1/N}`). The section's `N ≥ 4` and the coprimality of `u, v` are not needed (norm
argument; probe).

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 7
(`jis-2025-25.2.2-lem-7`). -/
public theorem_wanted prime_dvd_pow_add_of_dvd_radical_coeffs_gcd {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    (p : ℤ) ∣ (u : ℤ) ^ N + (-1) ^ (N + 1) * v

/-- For coprime `u, v`, `N ≥ 2` and `x^N - v` irreducible over `ℚ`, every prime dividing `D_n`
divides `N` (`n ≥ 1`): `D_n = 1` or `D_n` is a product of powers of primes dividing `N`. The
section assumes `N ≥ 4`; `N = 2, 3` also hold, `N = 1` fails.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 8
(`jis-2025-25.2.2-lem-8`). -/
public theorem_wanted prime_dvd_of_dvd_radical_coeffs_gcd {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    p ∣ N

/-- For coprime `u, v`, `N ≥ 2` and `x^N - v` irreducible over `ℚ`, if
`u^N + (-1)^{N+1} v` and `N` are coprime then `D_n = 1` for all `n ≥ 1`. The section assumes
`N ≥ 4`; `N = 2, 3` also hold, `N = 1` fails.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 9
(`jis-2025-25.2.2-cor-9`). -/
public theorem_wanted gcd_radical_expansion_coeffs_eq_one_of_coprime {N u v : ℕ} (hN : 2 ≤ N)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (hM : IsCoprime ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) (N : ℤ)) (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) = 1

end

end MetaMathlibExt
