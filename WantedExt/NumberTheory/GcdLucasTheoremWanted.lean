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

/-- **Unique integer coordinates of powers of $u + v^{1/N}$.** Let $N$ be a natural number with
at least two distinct prime divisors, let $u, v$ be coprime positive integers such that
$x^N - v$ is irreducible over $\mathbb{Q}$, and let $\theta = v^{1/N}$ be the positive real
$N$-th root of $v$. Then for every natural number $n$ there is exactly one tuple of integers
$(a_0, \dots, a_{N-1})$ with $(u + \theta)^n = \sum_{i=0}^{N-1} a_i \theta^i$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 3
(`jis-2025-25.2.2-lem-3`). -/
public theorem_wanted existsUnique_radical_expansion_coeffs {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (n : ℕ) :
    ∃! a : Fin N → ℤ, ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ)

/-- **Coprime coefficients of $(u + v^{1/N})^n$ when $N$ has two distinct prime factors.** Let
$N$ be a natural number with at least two distinct prime divisors, let $u, v$ be coprime positive
integers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let $\theta = v^{1/N}$ be the
positive real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$ and $0 \le i \le N - 1$) be
integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. Then for
every $n \ge 1$ the greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$ is $1$.

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

/-- **$u^N + (-1)^{N+1} v$ is coprime to $u$ and to $v$.** Let $u, v$ be coprime positive integers
and let $N \ge 1$. Then $\gcd(u^N + (-1)^{N+1} v, u) = 1$ and $\gcd(u^N + (-1)^{N+1} v, v) = 1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 5
(`jis-2025-25.2.2-lem-5`). -/
public theorem_wanted gcd_pow_add_neg_one_pow_mul_eq_one {N u v : ℕ} (hN : 1 ≤ N)
    (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v) :
    Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) u = 1 ∧
      Int.gcd ((u : ℤ) ^ N + (-1) ^ (N + 1) * v) v = 1

/-- **$p$ divides $\binom{p^r a}{p^s b}$ when $r > s$.** Let $p$ be a prime, let $r > s$ be
natural numbers, and let $a, b$ be natural numbers not divisible by $p$. Then
$p \mid \binom{p^r a}{p^s b}$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 14
(`jis-2025-25.2.2-cor-14`). -/
public theorem_wanted prime_dvd_choose_pow_mul_pow_mul {p a b r s : ℕ} (hp : p.Prime)
    (hrs : s < r) (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : p ∣ (p ^ r * a).choose (p ^ s * b)

/-- **Binomial coefficients $\binom{p^r a}{p^r b}$ modulo $p$.** Let $p$ be a prime, let $r \ge 1$,
and let $a, b$ be natural numbers not divisible by $p$. Then
$\binom{p^r a}{p^r b} \equiv \binom{a}{b} \pmod{p}$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Corollary 15
(`jis-2025-25.2.2-cor-15`). -/
public theorem_wanted choose_pow_mul_modEq {p a b r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) : (p ^ r * a).choose (p ^ r * b) ≡ a.choose b [MOD p]

/-- **Gcd of the coefficients of $(u + \sqrt{v})^n$.** Let $u, v$ be coprime positive integers
with $\sqrt{v}$ irrational, let $a_n, b_n$ (for natural $n$) be integers with
$(u + \sqrt{v})^n = a_n + b_n \sqrt{v}$ for every $n \ge 1$, and let $D_n \ge 0$ be the greatest
common divisor of $a_n$ and $b_n$. Then for every $n \ge 1$:
(a) if $u^2 - v$ is odd, then $D_n = 1$;
(b) if $u^2 - v \equiv 2 \pmod 4$, then $D_{2n-1} = 2^{n-1}$ and $D_{2n} = 2^n$;
(c) if $u^2 - v \equiv 4 \pmod 8$, then $D_{3n-2} = 2^{3n-3}$, $D_{3n-1} = 2^{3n-2}$ and
$D_{3n} = 2^{3n}$;
(d) if $u^2 - v \equiv 0 \pmod 8$, then $D_n = 2^{n-1}$.

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

/-- **Gcd of the coefficients of $(u + v^{1/p})^n$ for an odd prime $p$.** Let $p$ be an odd
prime, let $u, v$ be coprime positive integers such that $\theta = v^{1/p}$, the positive real
$p$-th root of $v$, is irrational, and let $a_{n,i}$ (for natural $n$ and $0 \le i \le p - 1$) be
integers with $(u + \theta)^n = \sum_{i=0}^{p-1} a_{n,i} \theta^i$ for every $n \ge 1$. Write
$D_n$ for the nonnegative greatest common divisor of $a_{n,0}, \dots, a_{n,p-1}$. Then:
(a) if $p \nmid u^p + v$, then $D_n = 1$ for every $n \ge 1$;
(b) if $u^p + v = mp$ for a natural number $m$ with $p \nmid m$, then $D_{np+i} = p^n$ for all
natural numbers $n, i$ with $i \le p - 1$ and $np + i \ge 1$;
(c) if $p^2 \mid u^p + v$, then $D_{n(p-1)+i} = p^n$ for all natural numbers $n, i$ with
$1 \le i \le p - 1$.

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

/-- **The coefficient gcd of $(u + v^{1/N})^n$ divides that of $(u + v^{1/N})^{n+1}$.** Let
$N, u, v$ be natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let
$\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$
and $0 \le i \le N - 1$) be integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$
for every $n \ge 1$. Write $D_n$ for the nonnegative greatest common divisor of
$a_{n,0}, \dots, a_{n,N-1}$. Then $D_n \mid D_{n+1}$ for every $n \ge 1$.

This holds without the paper's standing assumptions $N \ge 4$ and $\gcd(u, v) = 1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 4
(`jis-2025-25.2.2-lem-4`). -/
public theorem_wanted gcd_radical_expansion_coeffs_dvd_succ {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) ∣ Finset.univ.gcd (a (n + 1))

/-- **Common prime factors of $u^N + (-1)^{N+1} v$ and the coefficient gcd divide $N$.** Let
$N \ge 2$, let $u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over
$\mathbb{Q}$, let $\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$
(for natural $n$ and $0 \le i \le N - 1$) be integers with
$(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. Write $D_n$ for the
nonnegative greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$. Then for every $n \ge 1$,
every prime $p$ dividing $\gcd(u^N + (-1)^{N+1} v, D_n)$ divides $N$.

The paper assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails, since then
$D_n = (u + v)^n$.

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

/-- **Primes dividing the coefficient gcd of $(u + v^{1/N})^n$ divide the norm.** Let $u, v, N$
be natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$. Write $\theta = v^{1/N}$
for the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ be integers ($n \ge 1$,
$0 \le i < N$) with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every $n \ge 1$. If
$n \ge 1$ and $p$ is a prime dividing $D_n = \gcd(a_{n,0}, \dots, a_{n,N-1})$, then $p$ divides
$u^N + (-1)^{N+1} v$, the norm of $u + \theta$.

The paper's section assumes $N \ge 4$ and $u, v$ coprime; neither is needed here.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 7
(`jis-2025-25.2.2-lem-7`). -/
public theorem_wanted prime_dvd_pow_add_of_dvd_radical_coeffs_gcd {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hpd : (p : ℤ) ∣ Finset.univ.gcd (a n)) :
    (p : ℤ) ∣ (u : ℤ) ^ N + (-1) ^ (N + 1) * v

/-- **Primes dividing the coefficient gcd of $(u + v^{1/N})^n$ divide $N$.** Let $N \ge 2$ and
let $u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$. Write
$\theta = v^{1/N}$ for the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ be integers
($n \ge 1$, $0 \le i < N$) with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$ for every
$n \ge 1$. If $n \ge 1$ and $p$ is a prime dividing $D_n = \gcd(a_{n,0}, \dots, a_{n,N-1})$,
then $p$ divides $N$.

The paper's section assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails
(there $D_n = (u + v)^n$).

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

/-- **Coprime coefficients when $u^N + (-1)^{N+1} v$ is coprime to $N$.** Let $N \ge 2$, let
$u, v$ be coprime natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let
$\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$
and $0 \le i \le N - 1$) be integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$
for every $n \ge 1$. If $u^N + (-1)^{N+1} v$ and $N$ are coprime integers, then for every
$n \ge 1$ the greatest common divisor of $a_{n,0}, \dots, a_{n,N-1}$ is $1$.

The paper assumes $N \ge 4$; the cases $N = 2, 3$ also hold, while $N = 1$ fails.

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
