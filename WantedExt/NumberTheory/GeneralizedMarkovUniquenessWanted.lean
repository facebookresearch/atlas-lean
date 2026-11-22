/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Generalized Markov triple.** For a natural number $k$, a $k$-generalized Markov triple
is a triple $(a, b, c)$ of positive integers satisfying the $k$-generalized Markov equation
$\mathrm{GME}(k)$:
$$a^2 + b^2 + c^2 + k(bc + ca + ab) = (3 + 3k)abc.$$
For $k = 0$ these are the classical Markov triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovTriple (k a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c

/-- **$(1, 1, 1)$ is a generalized Markov triple.** For every natural number $k$, the triple
$(1, 1, 1)$ is a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public theorem isGenMarkovTriple_one_one_one (k : ℕ) : IsGenMarkovTriple k 1 1 1 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.one_pos, ?_⟩
  ring

/-- **The Markov triple $(1, 1, 2)$.** The triple $(1, 1, 2)$ is a $0$-generalized Markov
triple, that is, a classical Markov triple: $1^2 + 1^2 + 2^2 = 3 \cdot 1 \cdot 1 \cdot 2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.1. -/
public theorem isGenMarkovTriple_zero_one_one_two : IsGenMarkovTriple 0 1 1 2 := by
  refine ⟨Nat.one_pos, Nat.one_pos, Nat.two_pos, ?_⟩
  norm_num

/-- **Generalized Markov number.** Let $k$ be a natural number. A natural number $b$ is a
$k$-generalized Markov number when there are natural numbers $a$ and $c$ such that
$(a, b, c)$ is a $k$-generalized Markov triple.

Since the $k$-generalized Markov equation is symmetric in its three variables, this is the same
as $b$ being an entry, in any position, of some $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.2. -/
public def IsGenMarkovNumber (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c

/-- **Unique maximal generalized Markov triple.** Let $k$ and $b$ be natural numbers. The number
$b$ is the maximum of a unique $k$-generalized Markov triple up to order if there is a
$k$-generalized Markov triple $(a, b, c)$ with $a \le b$ and $c \le b$, and every
$k$-generalized Markov triple $(a', b, c')$ with $a' \le b$ and $c' \le b$ satisfies
$(a', c') = (a, c)$ or $(a', c') = (c, a)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Conjecture 1.8. -/
public def HasUniqueMaxGenMarkovTriple (k b : ℕ) : Prop :=
  ∃ a c, IsGenMarkovTriple k a b c ∧ a ≤ b ∧ c ≤ b ∧
    ∀ a' c', IsGenMarkovTriple k a' b c' → a' ≤ b → c' ≤ b →
      (a' = a ∧ c' = c) ∨ (a' = c ∧ c' = a)

/-- **A unique maximum is a generalized Markov number.** Let $k$ and $b$ be natural numbers.
If $b$ is the maximum of a unique $k$-generalized Markov triple up to order, then $b$ is a
$k$-generalized Markov number.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Conjecture 1.8. -/
public theorem HasUniqueMaxGenMarkovTriple.isGenMarkovNumber {k b : ℕ}
    (h : HasUniqueMaxGenMarkovTriple k b) : IsGenMarkovNumber k b := by
  obtain ⟨a, c, h, -⟩ := h
  exact ⟨a, c, h⟩

/-- **Number of solutions of $x^2 + kx + 1 \equiv 0 \pmod b$.** For natural numbers $k$ and
$b$, this is the number of integers $x$ with $0 \le x < b$ such that $b$ divides
$x^2 + kx + 1$. For $b = 0$ it is $0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.5. -/
public def genMarkovCongruenceCount (k b : ℕ) : ℕ :=
  ((range b).filter fun x => b ∣ x ^ 2 + k * x + 1).card

/-- **The congruence $x^2 + 1 \equiv 0 \pmod 5$ has two solutions.** Exactly two integers $x$
with $0 \le x < 5$ satisfy $x^2 + 1 \equiv 0 \pmod 5$.

They are $x = 2$ and $x = 3$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.2. -/
public theorem genMarkovCongruenceCount_zero_five : genMarkovCongruenceCount 0 5 = 2 := by
  decide

/-- **Uniqueness criterion via the congruence $x^2 + kx + 1 \equiv 0 \pmod{b}$.** Let $k$ be a
natural number and let $b$ be a $k$-generalized Markov number with $b \ne 1$ and $b \ne k + 2$.
If the congruence $x^2 + kx + 1 \equiv 0 \pmod{b}$ has at most two solutions $x$ with
$0 \le x < b$, then $b$ is the maximum of a unique $k$-generalized Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.5. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_of_congruenceCount_le_two {k b : ℕ}
    (hb : IsGenMarkovNumber k b) (hb1 : b ≠ 1) (hbk : b ≠ k + 2)
    (hcount : genMarkovCongruenceCount k b ≤ 2) : HasUniqueMaxGenMarkovTriple k b

/-- **Generalized Markov numbers $p$ and $2p$ are unique maxima.** Let $k$ be a natural number
and $p$ a prime. If $b$ is a $k$-generalized Markov number with $b = p$ or $b = 2p$, then $b$ is
the maximum of a unique $k$-generalized Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.6. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_prime {k b p : ℕ} (hb : IsGenMarkovNumber k b)
    (hp : p.Prime) (hbp : b = p ∨ b = 2 * p) : HasUniqueMaxGenMarkovTriple k b

/-- **Uniqueness for prime powers $p^m$ and $2p^m$ under conditions on $k$.** Let $k$ and $m$ be
natural numbers with $m \ge 2$ and let $p$ be a prime. Suppose that $k = 2$; or that $k \ge 4$ is
even and $p^2$ divides neither $k/2 + 1$ nor $k/2 - 1$; or that $k$ is odd and $p^2$ divides
neither $k + 2$ nor $k - 2$ in $\mathbb{Z}$. If $b$ is a $k$-generalized Markov number with
$b = p^m$ or $b = 2p^m$, then $b$ is the maximum of a unique $k$-generalized Markov triple up to
order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.7. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_prime_pow {k b p m : ℕ}
    (hb : IsGenMarkovNumber k b) (hp : p.Prime) (hm : 2 ≤ m) (hbp : b = p ^ m ∨ b = 2 * p ^ m)
    (hk : k = 2 ∨ (4 ≤ k ∧ Even k ∧ ¬ p ^ 2 ∣ k / 2 + 1 ∧ ¬ p ^ 2 ∣ k / 2 - 1) ∨
      (Odd k ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) + 2 ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) - 2)) :
    HasUniqueMaxGenMarkovTriple k b

/-- **Uniqueness for odd prime powers $p^m$ and $2p^m$ with $p \nmid k^2 - 4$.** Let $k$ and $m$
be natural numbers with $m \ge 2$, and let $p$ be an odd prime that does not divide $k^2 - 4$ in
$\mathbb{Z}$. If $b$ is a $k$-generalized Markov number with $b = p^m$ or $b = 2p^m$, then $b$ is
the maximum of a unique $k$-generalized Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 4.10. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_odd_prime_pow {k b p m : ℕ}
    (hb : IsGenMarkovNumber k b) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m) (hk : ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4) :
    HasUniqueMaxGenMarkovTriple k b

open Classical in
/-- **Bound on the number of generalized Markov triples with a given maximum.** Let $k$ be a
natural number such that either $k \ge 4$ is even and $k/2 + 1$ and $k/2 - 1$ are squarefree,
or $k$ is odd and the integers $k + 2$ and $k - 2$ are squarefree. Let $b$ be a $k$-generalized
Markov number that is not divisible by $4$, and suppose that the number $n$ of odd primes
dividing $b$ is at least $1$; equivalently, $b = p_1^{a_1} \cdots p_n^{a_n}$ or
$b = 2 p_1^{a_1} \cdots p_n^{a_n}$ for distinct odd primes $p_1, \dots, p_n$ with $n \ge 1$.
Then there are at most $2^{n-1}$ pairs of natural numbers $(a, c)$ with $a \le c \le b$ such
that $(a, b, c)$ is a $k$-generalized Markov triple; that is, $b$ is the maximum of at most
$2^{n-1}$ such triples up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 4.20. -/
public theorem_wanted card_maxGenMarkovTriples_le {k b : ℕ}
    (hk : (4 ≤ k ∧ Even k ∧ Squarefree (k / 2 + 1) ∧ Squarefree (k / 2 - 1)) ∨
      (Odd k ∧ Squarefree ((k : ℤ) + 2) ∧ Squarefree ((k : ℤ) - 2)))
    (hb : IsGenMarkovNumber k b) (hb4 : ¬ 4 ∣ b)
    (hn : 1 ≤ (b.primeFactors.filter (· ≠ 2)).card) :
    ((range (b + 1) ×ˢ range (b + 1)).filter fun q =>
        q.1 ≤ q.2 ∧ IsGenMarkovTriple k q.1 b q.2).card ≤
      2 ^ ((b.primeFactors.filter (· ≠ 2)).card - 1)

/-- **Generalized Markov triples are pairwise coprime.** If $(a, b, c)$ is a $k$-generalized
Markov triple, then $\gcd(a, b) = \gcd(b, c) = \gcd(a, c) = 1$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.3 (citing Gyoda and
Matsushita, Corollary 8). -/
public theorem_wanted IsGenMarkovTriple.pairwise_coprime {k a b c : ℕ}
    (h : IsGenMarkovTriple k a b c) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c

/-- **The generalized Markov equation and the generalized second Markov equation.** Let
$k \in \mathbb{N}$ and let $a, b, c$ be rational numbers. Put $x = (3 + 3k)a - k$,
$y = (3 + 3k)b - k$ and $z = (3 + 3k)c - k$. Then
$a^2 + b^2 + c^2 + k(bc + ca + ab) = (3 + 3k)abc$ if and only if
$x^2 + y^2 + z^2 + (k^2 + 2k)(x + y + z) + 2k^3 + 3k^2 = xyz$. The first equation is the
$k$-generalized Markov equation $\mathrm{GME}(k)$ and the second the $k$-generalized second
Markov equation $\mathrm{GSME}(k)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.4. -/
public theorem_wanted genMarkov_iff_genSecondMarkov (k : ℕ) (a b c : ℚ) :
    a ^ 2 + b ^ 2 + c ^ 2 + k * (b * c + c * a + a * b) = (3 + 3 * k) * a * b * c ↔
      let x := (3 + 3 * k) * a - k
      let y := (3 + 3 * k) * b - k
      let z := (3 + 3 * k) * c - k
      x ^ 2 + y ^ 2 + z ^ 2 + ((k : ℚ) ^ 2 + 2 * k) * (x + y + z) + 2 * (k : ℚ) ^ 3 +
          3 * (k : ℚ) ^ 2 = x * y * z

/-- **Vieta jumping for the second generalized Markov equation.** Let $k$ be a natural number
and let $a, b, c$ be integers with

$$a^2 + b^2 + c^2 + (k^2 + 2k)(a + b + c) + 2k^3 + 3k^2 = abc.$$

Then the triples $(a, ab - c - k^2 - 2k, b)$ and $(b, bc - a - k^2 - 2k, c)$ satisfy the same
equation.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.6. -/
public theorem_wanted genSecondMarkov_vieta (k : ℕ) {a b c : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c) :
    (let c' := a * b - c - (k : ℤ) ^ 2 - 2 * k;
      a ^ 2 + c' ^ 2 + b ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + c' + b) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = a * c' * b) ∧
    (let a' := b * c - a - (k : ℤ) ^ 2 - 2 * k;
      b ^ 2 + a' ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (b + a' + c) + 2 * (k : ℤ) ^ 3 +
        3 * (k : ℤ) ^ 2 = b * a' * c)

/-- **Trace identities in $\mathrm{SL}(2, \mathbb{Z})$.** For all $A, B \in \mathrm{SL}(2,
\mathbb{Z})$ we have $\operatorname{tr} A = \operatorname{tr} A^{-1}$,
$\operatorname{tr}(AB) = \operatorname{tr} A \cdot \operatorname{tr} B -
\operatorname{tr}(AB^{-1})$, and $A^2 = (\operatorname{tr} A) A - I$, where $I$ is the
identity matrix.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.6 (citing Aigner, Lemma 4.2). -/
public theorem_wanted specialLinearGroup_two_trace_identities
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) ∧
      Matrix.trace ((A * B : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℤ) -
          Matrix.trace ((A * B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
            Matrix (Fin 2) (Fin 2) ℤ) ∧
      (A : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 =
        Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) • (A : Matrix (Fin 2) (Fin 2) ℤ) - 1

/-- **At most two solutions of $x^2 + kx + 1 \equiv 0$ modulo a prime.** For every prime $p$
and every $k \in \mathbb{N}$, at most two integers $x$ with $0 \le x < p$ satisfy
$x^2 + kx + 1 \equiv 0 \pmod p$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.9. -/
public theorem_wanted genMarkovCongruenceCount_prime_le_two {p : ℕ} (hp : p.Prime) (k : ℕ) :
    genMarkovCongruenceCount k p ≤ 2

/-- **At most two solutions of $x^2 + kx + 1 \equiv 0$ modulo an odd prime power.** Let $p$
be an odd prime, let $m \ge 2$ and let $k \in \mathbb{N}$ with $k^2 - 4 \not\equiv 0 \pmod p$.
Then at most two integers $x$ with $0 \le x < p^m$ satisfy
$x^2 + kx + 1 \equiv 0 \pmod{p^m}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.11. -/
public theorem_wanted genMarkovCongruenceCount_prime_pow_le_two {p m k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hk : ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4) :
    genMarkovCongruenceCount k (p ^ m) ≤ 2

/-- **An even generalized Markov number forces $k$ to be even.** Let $k$ be a natural number. If
some $k$-generalized Markov number $b$ is even, then $k$ is even.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.13. -/
public theorem_wanted even_of_even_genMarkovNumber {k b : ℕ} (hb : IsGenMarkovNumber k b)
    (he : Even b) : Even k

/-- **Generalized Markov numbers divisible by $4$.** Let $k$ be a natural number. If some
$k$-generalized Markov number is divisible by $4$, then $k \equiv 2 \pmod{4}$.

Source: Only the first claim of Proposition 4.14 is stated; its "in particular" parity
consequence is omitted because its displayed fraction is garbled in the record.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.14. -/
public theorem_wanted mod_four_eq_two_of_four_dvd_genMarkovNumber {k b : ℕ}
    (hb : IsGenMarkovNumber k b) (h4 : 4 ∣ b) : k % 4 = 2

/-- **Large odd primes do not divide $k^2 - 4$.** Let $p$ be an odd prime and $k$ a natural
number. If either $k \ge 4$ is even and $p > k/2 + 1$, or $k$ is odd and $p > k + 2$, then $p$
does not divide $k^2 - 4$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.15. -/
public theorem_wanted not_dvd_sq_sub_four_of_large_prime {k p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : (4 ≤ k ∧ Even k ∧ k / 2 + 1 < p) ∨ (Odd k ∧ k + 2 < p)) :
    ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4

/-- **Discriminant condition for prime-power generalized Markov numbers.** Let $p$ be an odd
prime and $m \ge 2$, and suppose that some $k$-generalized Markov number $b$ equals $p^m$ or
$2p^m$. Suppose moreover that either $k \ge 4$ is even and $p^2$ divides neither $k/2 + 1$ nor
$k/2 - 1$, or $k$ is odd and $p^2$ divides neither $k + 2$ nor $k - 2$. Then $p$ does not
divide $k^2 - 4$.

As printed (without the Markov-number hypothesis) Proposition 4.16 is false: $k = 4$, $p = 3$
satisfy the divisibility conditions ($9 \nmid 3$, $9 \nmid 1$) but $3 \mid 12$; the paper's
proof assumes $b = p^m$ is a $k$-generalized Markov number and uses $m \ge 2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.16 and its proof. -/
public theorem_wanted not_dvd_sq_sub_four_of_genMarkovNumber_prime_pow {k p m b : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : 2 ≤ m) (hb : IsGenMarkovNumber k b)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m)
    (hk : (4 ≤ k ∧ Even k ∧ ¬ p ^ 2 ∣ k / 2 + 1 ∧ ¬ p ^ 2 ∣ k / 2 - 1) ∨
      (Odd k ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) + 2 ∧ ¬ (p : ℤ) ^ 2 ∣ (k : ℤ) - 2)) :
    ¬ (p : ℤ) ∣ (k : ℤ) ^ 2 - 4

/-- **2-generalized Markov triples are squares of Markov triples.** If $(a, b, c)$ is a Markov
triple, that is, a $0$-generalized Markov triple, then $(a^2, b^2, c^2)$ is a $2$-generalized
Markov triple. Conversely, for every $2$-generalized Markov triple $(A, B, C)$ there is a Markov
triple $(a, b, c)$ with $A = a^2$, $B = b^2$ and $C = c^2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.17 (citing Gyoda and
Matsushita, Theorem 2.9). -/
public theorem_wanted genMarkovTriple_two_iff_sq :
    (∀ a b c : ℕ, IsGenMarkovTriple 0 a b c → IsGenMarkovTriple 2 (a ^ 2) (b ^ 2) (c ^ 2)) ∧
      ∀ A B C : ℕ, IsGenMarkovTriple 2 A B C →
        ∃ a b c : ℕ, A = a ^ 2 ∧ B = b ^ 2 ∧ C = c ^ 2 ∧ IsGenMarkovTriple 0 a b c

/-- **Uniqueness criterion for classical Markov numbers.** Let $b \ne 1, 2$ be a Markov number
(a $0$-generalized Markov number). If the congruence $x^2 + 1 \equiv 0 \pmod{b}$ has at most
two solutions $x$ with $0 \le x < b$, then $b$ is the maximum of a unique Markov triple up to
order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.2 (citing Aigner,
Corollary 3.17). -/
public theorem_wanted markov_hasUniqueMaxTriple_of_congruenceCount_le_two {b : ℕ}
    (hb : IsGenMarkovNumber 0 b) (hb1 : b ≠ 1) (hb2 : b ≠ 2)
    (hcount : genMarkovCongruenceCount 0 b ≤ 2) : HasUniqueMaxGenMarkovTriple 0 b

/-- **Uniqueness for Markov numbers $p^m$ and $2p^m$ with $p$ an odd prime.** Let $p$ be an odd
prime and $m \ge 1$. If $b = p^m$ or $b = 2p^m$ is a Markov number (a $0$-generalized Markov
number), then $b$ is the maximum of a unique Markov triple up to order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.3 (citing Aigner,
Corollary 3.20). -/
public theorem_wanted markov_hasUniqueMaxTriple_odd_prime_pow {b p m : ℕ}
    (hb : IsGenMarkovNumber 0 b) (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hbp : b = p ^ m ∨ b = 2 * p ^ m) : HasUniqueMaxGenMarkovTriple 0 b

/-- **Markov triples with a common characteristic number agree up to order.** Let $m \ge 5$
and let $(m, m_2, m_3)$ and $(m, n_2, n_3)$ be Markov triples (that is, $0$-generalized Markov
triples) with $m_2, m_3, n_2, n_3 \le m$. Suppose some integer $x$ with $0 < x < m$ satisfies
$m_2 x \equiv \pm m_3 \pmod{m}$ and $n_2 x \equiv \pm n_3 \pmod{m}$, where the two signs are
chosen independently. Then $(m_2, m_3) = (n_2, n_3)$ or $(m_2, m_3) = (n_3, n_2)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 1.11 (citing Aigner,
Proposition 3.15). -/
public theorem_wanted markov_eq_of_characteristic_number_eq {m m₂ m₃ n₂ n₃ x : ℕ}
    (hm : 5 ≤ m) (h₁ : IsGenMarkovTriple 0 m m₂ m₃) (h₂ : IsGenMarkovTriple 0 m n₂ n₃)
    (hm₁ : m₂ ≤ m ∧ m₃ ≤ m) (hm₂ : n₂ ≤ m ∧ n₃ ≤ m) (hx : 0 < x ∧ x < m)
    (hu₁ : (m : ℤ) ∣ m₂ * x - m₃ ∨ (m : ℤ) ∣ m₂ * x + m₃)
    (hu₂ : (m : ℤ) ∣ n₂ * x - n₃ ∨ (m : ℤ) ∣ n₂ * x + n₃) :
    (m₂ = n₂ ∧ m₃ = n₃) ∨ (m₂ = n₃ ∧ m₃ = n₂)

/-! ### Part 2: Markov trees, generalized Cohn trees, Farey tree and fraction labeling -/

/-- **Vieta jumping of generalized Markov triples.** For a natural number $k$, the left Vieta
jumping sends a triple $(a, b, c)$ of natural numbers to
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and the right Vieta jumping sends it to
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, where division by $0$ gives $0$. The left jumping
is indexed by the boolean value false and the right one by true.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovVieta (k : ℕ) : Bool → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ
  | false, (a, b, c) => (a, (a ^ 2 + k * a * b + b ^ 2) / c, b)
  | true, (a, b, c) => (b, (b ^ 2 + k * b * c + c ^ 2) / a, c)

/-- **The wide generalized Markov tree.** Fix a natural number $k$. The wide $k$-generalized
Markov tree $\mathrm{WMT}(k)$ is the binary tree of triples of natural numbers with root
$(1, 1, 1)$ in which a vertex $(a, b, c)$ has left child
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and right child
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$, the left and right Vieta jumpings. For a path $w$,
a finite sequence of left and right steps, the vertex of $\mathrm{WMT}(k)$ at $w$ is the triple
reached from the root by taking the steps of $w$ in order; the empty path gives the root.

The quotients are divisions of natural numbers, rounded down, with division by $0$ giving $0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def wideGenMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  w.foldl (fun t d => genMarkovVieta k d t) (1, 1, 1)

/-- **Generalized Markov tree.** For a natural number $k$ and a finite sequence $w$ of left and
right steps, the vertex of the $k$-generalized Markov tree $MT(k)$ at $w$ is the vertex of the
wide $k$-generalized Markov tree $WMT(k)$ reached from its root by one left step followed by the
steps of $w$ in order. Thus $MT(k)$ is the full subtree of $WMT(k)$ rooted at the left child of
the root.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def genMarkovTree (k : ℕ) (w : List Bool) : ℕ × ℕ × ℕ :=
  wideGenMarkovTree k (false :: w)

/-- **Children in the wide generalized Markov tree are Vieta jumpings.** For every natural
number $k$, every path $w$ and every direction $d$ (left or right), the vertex of the wide
$k$-generalized Markov tree $\mathrm{WMT}(k)$ at the path $w$ followed by one step in direction
$d$ is the image of the vertex at $w$ under the Vieta jumping in direction $d$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem wideGenMarkovTree_append_singleton (k : ℕ) (w : List Bool) (d : Bool) :
    wideGenMarkovTree k (w ++ [d]) = genMarkovVieta k d (wideGenMarkovTree k w) := by
  simp [wideGenMarkovTree, List.foldl_append]

/-- **Root of the generalized Markov tree.** For every natural number $k$, the root of the
$k$-generalized Markov tree $MT(k)$, its vertex at the empty path, is $(1, k + 2, 1)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem genMarkovTree_nil (k : ℕ) : genMarkovTree k [] = (1, k + 2, 1) := by
  simp only [genMarkovTree, wideGenMarkovTree, List.foldl_cons, List.foldl_nil, genMarkovVieta]
  congr 2
  rw [Nat.div_one]
  ring

/-- **Left child of the root of the classical Markov tree.** For $k = 0$, the vertex of the
Markov tree $MT(0)$ reached from the root by one left step is $(1, 5, 2)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem genMarkovTree_zero_false : genMarkovTree 0 [false] = (1, 5, 2) := by
  decide

/-- **Generalized Markov triples in the wide Markov tree.** Let $k$ be a natural number. Every
vertex of the wide $k$-generalized Markov tree $\mathrm{WMT}(k)$ is a $k$-generalized Markov
triple. Moreover, every $k$-generalized Markov triple $(a, b, c)$ with $a < b$ and $c < b$ is
the vertex of $\mathrm{WMT}(k)$ at exactly one path that starts with a left step, and at exactly
one path that starts with a right step.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.1 (citing Gyoda and
Matsushita, Theorem 1). -/
public theorem_wanted wideGenMarkovTree_isGenMarkovTriple_and_twice (k : ℕ) :
    (∀ w, IsGenMarkovTriple k (wideGenMarkovTree k w).1 (wideGenMarkovTree k w).2.1
      (wideGenMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a < b → c < b →
      (∃! w, wideGenMarkovTree k (false :: w) = (a, b, c)) ∧
        ∃! w, wideGenMarkovTree k (true :: w) = (a, b, c)

/-- **Vertices of the generalized Markov tree.** For every natural number $k$, every vertex of
the $k$-generalized Markov tree $MT(k)$ is a $k$-generalized Markov triple, and for every
$k$-generalized Markov triple $(a, b, c)$ with $a < b$ and $c < b$ there is exactly one path $w$
such that the vertex of $MT(k)$ at $w$ is $(a, b, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 2.2. -/
public theorem_wanted genMarkovTree_isGenMarkovTriple_and_once (k : ℕ) :
    (∀ w, IsGenMarkovTriple k (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a < b → c < b → ∃! w, genMarkovTree k w = (a, b, c)

/-- **Vieta jumping identities for generalized Markov triples.** If $(a, b, c)$ is a
$k$-generalized Markov triple, then, as integers,
$a^2 + kab + b^2 = c\,((3 + 3k)ab - c - k(a + b))$ and
$b^2 + kbc + c^2 = a\,((3 + 3k)bc - a - k(b + c))$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2 (display after
Corollary 2.2). -/
public theorem_wanted IsGenMarkovTriple.vieta_eq {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    ((a : ℤ) ^ 2 + k * a * b + b ^ 2 = c * ((3 + 3 * k) * a * b - c - k * (a + b))) ∧
      ((b : ℤ) ^ 2 + k * b * c + c ^ 2 = a * ((3 + 3 * k) * b * c - a - k * (b + c)))

/-- **Induced solution of the generalized second Markov equation.** For a natural number $k$,
a triple $(a, b, c)$ of integers is an induced positive solution of the $k$-generalized second
Markov equation $\mathrm{GSME}(k)$ when $a, b, c > 0$,
$$a^2 + b^2 + c^2 + (k^2 + 2k)(a + b + c) + 2k^3 + 3k^2 = abc,$$
and $3 + 3k$ divides each of $a + k$, $b + k$ and $c + k$.

Equivalently, $(a + k)/(3 + 3k)$, $(b + k)/(3 + 3k)$ and $(c + k)/(3 + 3k)$ are integers; they
are automatically positive since $a, b, c > 0$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public def IsInducedGenSecondMarkovSolution (k : ℕ) (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧
    a ^ 2 + b ^ 2 + c ^ 2 + ((k : ℤ) ^ 2 + 2 * k) * (a + b + c) + 2 * (k : ℤ) ^ 3 +
      3 * (k : ℤ) ^ 2 = a * b * c ∧
    (3 + 3 * (k : ℤ)) ∣ a + k ∧ (3 + 3 * (k : ℤ)) ∣ b + k ∧ (3 + 3 * (k : ℤ)) ∣ c + k

/-- **The root induced solution of the generalized second Markov equation.** For every natural
number $k$, the triple $(3 + 2k, 3 + 2k, 3 + 2k)$, the image of $(1, 1, 1)$ under
$x \mapsto (3 + 3k)x - k$, is an induced positive solution of the $k$-generalized second
Markov equation $\mathrm{GSME}(k)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 2. -/
public theorem isInducedGenSecondMarkovSolution_root (k : ℕ) :
    IsInducedGenSecondMarkovSolution k (3 + 2 * k) (3 + 2 * k) (3 + 2 * k) := by
  refine ⟨by positivity, by positivity, by positivity, by ring, ⟨1, by ring⟩, ⟨1, by ring⟩,
    ⟨1, by ring⟩⟩

/-- **Vieta jumping preserves induced solutions of the generalized second Markov equation.** If
$(a, b, c)$ is an induced solution of the $k$-generalized second Markov equation
$\mathrm{GSME}(k)$, then so are $(a, ab - c - k^2 - 2k, b)$ and $(b, bc - a - k^2 - 2k, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.7. -/
public theorem_wanted IsInducedGenSecondMarkovSolution.vieta {k : ℕ} {a b c : ℤ}
    (h : IsInducedGenSecondMarkovSolution k a b c) :
    IsInducedGenSecondMarkovSolution k a (a * b - c - (k : ℤ) ^ 2 - 2 * k) b ∧
      IsInducedGenSecondMarkovSolution k b (b * c - a - (k : ℤ) ^ 2 - 2 * k) c

/-- **Vertices of the second generalized Markov tree.** For a natural number $k$, let $SMT(k)$
be the tree obtained from the $k$-generalized Markov tree $MT(k)$ by replacing each vertex
$(a, b, c)$ with the integer triple $((3 + 3k)a - k, (3 + 3k)b - k, (3 + 3k)c - k)$. Every vertex
of $SMT(k)$ is an induced solution of the $k$-generalized second Markov equation, and for every
induced solution $(a, b, c)$ with $a < b$ and $c < b$ there is exactly one path $w$ such that the
vertex of $SMT(k)$ at $w$ is $(a, b, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 2.8. -/
public theorem_wanted genSecondMarkovTree_induced_and_once (k : ℕ) :
    (∀ w, IsInducedGenSecondMarkovSolution k ((3 + 3 * k) * ((genMarkovTree k w).1 : ℤ) - k)
      ((3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - k)
      ((3 + 3 * k) * ((genMarkovTree k w).2.2 : ℤ) - k)) ∧
    ∀ a b c, IsInducedGenSecondMarkovSolution k a b c → a < b → c < b →
      ∃! w, ((3 + 3 * k) * ((genMarkovTree k w).1 : ℤ) - k,
        (3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - k,
        (3 + 3 * k) * ((genMarkovTree k w).2.2 : ℤ) - k) = (a, b, c)

/-- **The matrix $S$ of the generalized Cohn triple relation.** For a natural number $k$, $S$
is the $2 \times 2$ integer matrix

$$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}.$$

It is the matrix in the relation $Q = PR - S$ that defines $k$-generalized Cohn triples.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def genCohnS (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(k : ℤ), 0; 3 * (k : ℤ) ^ 2 + 3 * k, k]

/-- **The matrix $S$ vanishes for $k = 0$.** For $k = 0$, the matrix $S$ of the generalized
Cohn triple relation is the zero $2 \times 2$ matrix, so the relation $Q = PR - S$ reduces to
the classical Cohn relation $Q = PR$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 1.3. -/
public theorem genCohnS_zero : genCohnS 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [genCohnS]

/-- **Generalized Cohn matrices.** Let $k$ be a natural number. An integer $2 \times 2$ matrix
$P = (p_{ij})$ is a $k$-generalized Cohn matrix if $\det P = 1$, its entry $p_{12}$ is a
$k$-generalized Markov number, and its trace equals $(3 + 3k) p_{12} - k$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.1. -/
public def IsGenCohnMatrix (k : ℕ) (P : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  P.det = 1 ∧ ∃ n : ℕ, P 0 1 = n ∧ IsGenMarkovNumber k n ∧ P.trace = (3 + 3 * k) * n - k

/-- **Generalized Cohn triple.** Let $k$ be a natural number and let $S$ be the integer matrix
with rows $(k, 0)$ and $(3k^2 + 3k, k)$. A triple $(P, Q, R)$ of integer $2 \times 2$ matrices is
a $k$-generalized Cohn triple associated with natural numbers $(a, b, c)$ when $P$, $Q$ and $R$
are $k$-generalized Cohn matrices, $Q = PR - S$, the $(1, 2)$-entries of $P$, $Q$ and $R$ are
$a$, $b$ and $c$ respectively, and $(a, b, c)$ is a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public def IsGenCohnTriple (k : ℕ) (P Q R : Matrix (Fin 2) (Fin 2) ℤ) (a b c : ℕ) : Prop :=
  IsGenCohnMatrix k P ∧ IsGenCohnMatrix k Q ∧ IsGenCohnMatrix k R ∧ Q = P * R - genCohnS k ∧
    P 0 1 = a ∧ Q 0 1 = b ∧ R 0 1 = c ∧ IsGenMarkovTriple k a b c

/-- **Generalized Cohn triples give generalized Markov triples.** Let $k$ be a natural number.
If $(P, Q, R)$ is a $k$-generalized Cohn triple associated with $(a, b, c)$, then $(a, b, c)$ is
a $k$-generalized Markov triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 3.2. -/
public theorem IsGenCohnTriple.isGenMarkovTriple {k : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    {a b c : ℕ} (h : IsGenCohnTriple k P Q R a b c) : IsGenMarkovTriple k a b c :=
  h.2.2.2.2.2.2.2

/-- **The matrix $P_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $P_{1;\ell}$ is
the integer $2 \times 2$ matrix with first row $(\ell, 1)$ and second row
$(-\ell^2 + 2k\ell + 3\ell - 1, -\ell + 2k + 3)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnP1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![ℓ, 1; -ℓ ^ 2 + 2 * k * ℓ + 3 * ℓ - 1, -ℓ + 2 * k + 3]

/-- **The matrix $Q_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $Q_{1;\ell}$ is
the $2 \times 2$ integer matrix

$$\begin{pmatrix} k + \ell + 1 & 1 \\ k^2 - \ell^2 + 3k + \ell + 1 & k - \ell + 2 \end{pmatrix}.$$

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnQ1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![k + ℓ + 1, 1; (k : ℤ) ^ 2 - ℓ ^ 2 + 3 * k + ℓ + 1, k - ℓ + 2]

/-- **The matrix $R_{1;\ell}$.** For a natural number $k$ and an integer $\ell$, $R_{1;\ell}$ is
the $2 \times 2$ integer matrix

$$\begin{pmatrix} 2k + \ell + 2 & 1 \\ -\ell^2 - 2k\ell + 2k - \ell + 1 & -\ell + 1 \end{pmatrix}.$$

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnR1 (k : ℕ) (ℓ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2 * k + ℓ + 2, 1; -ℓ ^ 2 - 2 * k * ℓ + 2 * k - ℓ + 1, -ℓ + 1]

/-- **The matrices $P_{1;\ell}$, $Q_{1;\ell}$ and $R_{1;\ell}$ have determinant $1$.** For every
natural number $k$ and every integer $\ell$, the $2 \times 2$ integer matrices $P_{1;\ell}$,
$Q_{1;\ell}$ and $R_{1;\ell}$ (which depend on $k$) all have determinant $1$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public theorem genCohnPQR1_det (k : ℕ) (ℓ : ℤ) :
    (genCohnP1 k ℓ).det = 1 ∧ (genCohnQ1 k ℓ).det = 1 ∧ (genCohnR1 k ℓ).det = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [genCohnP1, genCohnQ1, genCohnR1, Matrix.det_fin_two_of] <;> ring

/-- **One step of the wide generalized Cohn tree.** Fix a natural number $k$ and let $S$ be the
matrix of the $k$-generalized Cohn triple relation. On triples $(P, Q, R)$ of $2 \times 2$
integer matrices, the left step (encoded by the Boolean false) sends $(P, Q, R)$ to its left
child $(P, PQ - S, Q)$, and the right step (encoded by true) sends it to its right child
$(Q, QR - S, R)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnStep (k : ℕ) : Bool →
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ →
      Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ
  | false, (P, Q, _) => (P, P * Q - genCohnS k, Q)
  | true, (_, Q, R) => (Q, Q * R - genCohnS k, R)

/-- **Paths of generalized Cohn steps.** Fix a natural number $k$ and let $S$ be the integer
$2 \times 2$ matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$. For a triple $T$ of integer
$2 \times 2$ matrices and a path $w$, a finite sequence of left and right moves, this is the
triple obtained from $T$ by applying the moves of $w$ in order, where a left move sends
$(P, Q, R)$ to $(P, PQ - S, Q)$ and a right move sends $(P, Q, R)$ to $(Q, QR - S, R)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.10. -/
public def genCohnPath (k : ℕ)
    (T : Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ)
    (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  w.foldl (fun T d => genCohnStep k d T) T

/-- **The wide generalized Cohn tree.** Fix a natural number $k$ and an integer $\ell$, and let
$S = \begin{pmatrix} k & 0 \\ 3k^2 + 3k & k \end{pmatrix}$. The wide $k$-generalized Cohn tree
$\mathrm{WGCT}(k, \ell)$ is the binary tree of triples of $2 \times 2$ integer matrices whose
root is $(P_{1;\ell}, Q_{1;\ell}, R_{1;\ell})$, where

$$P_{1;\ell}=\begin{pmatrix}\ell & 1\\ -\ell^2+2k\ell+3\ell-1 & -\ell+2k+3\end{pmatrix},$$

$$Q_{1;\ell}=\begin{pmatrix}k+\ell+1 & 1\\ k^2-\ell^2+3k+\ell+1 & k-\ell+2\end{pmatrix},$$

$$R_{1;\ell}=\begin{pmatrix}2k+\ell+2 & 1\\ -\ell^2-2k\ell+2k-\ell+1 & -\ell+1\end{pmatrix},$$

and in which a vertex $(P, Q, R)$ has left child $(P, PQ - S, Q)$ and right child
$(Q, QR - S, R)$. For a path $w$, a finite sequence of left and right steps, the vertex of
$\mathrm{WGCT}(k, \ell)$ at $w$ is the triple reached from the root by taking the steps of $w$ in
order; the empty path gives the root.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def wideGenCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  genCohnPath k (genCohnP1 k ℓ, genCohnQ1 k ℓ, genCohnR1 k ℓ) w

/-- **The $k$-generalized Cohn tree.** For $k \in \mathbb{N}$ and $\ell \in \mathbb{Z}$, the
$k$-generalized Cohn tree $\mathrm{GCT}(k, \ell)$ is the full subtree of the wide
$k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$ rooted at the left child of its root. For a
finite sequence $w$ of left and right moves, this is the vertex of $\mathrm{GCT}(k, \ell)$
reached from its root along $w$, that is, the vertex of $\mathrm{WGCT}(k, \ell)$ reached from
the root of $\mathrm{WGCT}(k, \ell)$ by one left move followed by the moves of $w$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public def genCohnTree (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ :=
  wideGenCohnTree k ℓ (false :: w)

/-- **Children in the wide generalized Cohn tree.** Let $k$ be a natural number, $\ell$ an
integer, and $S$ the integer matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$. For every path $w$
in the wide $k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$, if $(P, Q, R)$ is the vertex at
$w$, then the vertex at $w$ followed by a left step is $(P, PQ - S, Q)$ and the vertex at $w$
followed by a right step is $(Q, QR - S, R)$; that is, each child is obtained from its parent by
one generalized Cohn step.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.1. -/
public theorem wideGenCohnTree_append_singleton (k : ℕ) (ℓ : ℤ) (w : List Bool) (d : Bool) :
    wideGenCohnTree k ℓ (w ++ [d]) = genCohnStep k d (wideGenCohnTree k ℓ w) := by
  simp [wideGenCohnTree, genCohnPath, List.foldl_append]

/-- **Cohn steps reach every classical Cohn triple whose middle entry is largest.** Call a
$0$-generalized Cohn triple a Cohn triple; for $k = 0$ the matrix $S$ of the generalized Cohn
relation is zero, so the relation reads $Q = PR$. Call $(P, Q, R) \mapsto (P, PQ, Q)$ the left
step and $(P, Q, R) \mapsto (Q, QR, R)$ the right step. First, if $(P, Q, R)$ is a Cohn triple
associated with $(a, b, c)$ and $a \le b$, $c \le b$, then $(P, Q, R)$ is obtained by applying
finitely many left and right steps to some Cohn triple associated with $(1, 1, 1)$. Second, if
$(P, Q, R)$ is a Cohn triple associated with $(a, b, c)$, then the $(1, 2)$-entries of the left
step $(P, PQ, Q)$ are $(a, \lfloor (a^2 + b^2)/c \rfloor, b)$ and those of the right step
$(Q, QR, R)$ are $(b, \lfloor (b^2 + c^2)/a \rfloor, c)$: on $(1, 2)$-entries the steps are the
left and right Vieta jumpings of the Markov triple $(a, b, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.9 (citing Aigner,
Theorem 4.7). -/
public theorem_wanted cohnTriple_reachable :
    (∀ P Q R a b c, IsGenCohnTriple 0 P Q R a b c → a ≤ b → c ≤ b →
      ∃ P₀ Q₀ R₀ w, IsGenCohnTriple 0 P₀ Q₀ R₀ 1 1 1 ∧ genCohnPath 0 (P₀, Q₀, R₀) w = (P, Q, R)) ∧
    ∀ P Q R a b c d, IsGenCohnTriple 0 P Q R a b c →
      (genCohnStep 0 d (P, Q, R)).1 0 1 = (genMarkovVieta 0 d (a, b, c)).1 ∧
        (genCohnStep 0 d (P, Q, R)).2.1 0 1 = (genMarkovVieta 0 d (a, b, c)).2.1 ∧
        (genCohnStep 0 d (P, Q, R)).2.2 0 1 = (genMarkovVieta 0 d (a, b, c)).2.2

/-- **Cohn steps reach every generalized Cohn triple whose middle entry is largest.** Let
$k \in \mathbb{N}$ and let $S$ be the integer matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$.
Call $(P, Q, R) \mapsto (P, PQ - S, Q)$ the left step and $(P, Q, R) \mapsto (Q, QR - S, R)$ the
right step. First, if $(P, Q, R)$ is a $k$-generalized Cohn triple associated with $(a, b, c)$
and $a \le b$, $c \le b$, then $(P, Q, R)$ is obtained by applying finitely many left and
right steps to some $k$-generalized Cohn triple associated with $(1, 1, 1)$. Second, if
$(P, Q, R)$ is a $k$-generalized Cohn triple associated with $(a, b, c)$, then the
$(1, 2)$-entries of the left step $(P, PQ - S, Q)$ are
$(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$ and those of the right step $(Q, QR - S, R)$ are
$(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$: on $(1, 2)$-entries the steps are the left and
right Vieta jumpings of $(a, b, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 1.10. -/
public theorem_wanted genCohnTriple_reachable (k : ℕ) :
    (∀ P Q R a b c, IsGenCohnTriple k P Q R a b c → a ≤ b → c ≤ b →
      ∃ P₀ Q₀ R₀ w, IsGenCohnTriple k P₀ Q₀ R₀ 1 1 1 ∧ genCohnPath k (P₀, Q₀, R₀) w = (P, Q, R)) ∧
    ∀ P Q R a b c d, IsGenCohnTriple k P Q R a b c →
      (genCohnStep k d (P, Q, R)).1 0 1 = (genMarkovVieta k d (a, b, c)).1 ∧
        (genCohnStep k d (P, Q, R)).2.1 0 1 = (genMarkovVieta k d (a, b, c)).2.1 ∧
        (genCohnStep k d (P, Q, R)).2.2 0 1 = (genMarkovVieta k d (a, b, c)).2.2

/-- **Generalized Cohn triples associated with $(1, 1, 1)$.** Let $k$ be a natural number.
For an integer $\ell$, let $P_{1;\ell}$ be the integer matrix with rows $(\ell, 1)$ and
$(-\ell^2 + 2k\ell + 3\ell - 1, -\ell + 2k + 3)$, let $Q_{1;\ell}$ be the one with rows
$(k + \ell + 1, 1)$ and $(k^2 - \ell^2 + 3k + \ell + 1, k - \ell + 2)$, and let $R_{1;\ell}$ be
the one with rows $(2k + \ell + 2, 1)$ and $(-\ell^2 - 2k\ell + 2k - \ell + 1, -\ell + 1)$.
Then for every integer $\ell$, $(P_{1;\ell}, Q_{1;\ell}, R_{1;\ell})$ is a $k$-generalized Cohn
triple associated with $(1, 1, 1)$. Conversely, if $(P, Q, R)$ is a $k$-generalized Cohn triple
associated with $(1, 1, 1)$, then there is an integer $\ell$ with $P = P_{1;\ell}$,
$Q = Q_{1;\ell}$ and $R = R_{1;\ell}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.4. -/
public theorem_wanted isGenCohnTriple_one_iff (k : ℕ) :
    (∀ ℓ, IsGenCohnTriple k (genCohnP1 k ℓ) (genCohnQ1 k ℓ) (genCohnR1 k ℓ) 1 1 1) ∧
    ∀ P Q R, IsGenCohnTriple k P Q R 1 1 1 →
      ∃ ℓ, P = genCohnP1 k ℓ ∧ Q = genCohnQ1 k ℓ ∧ R = genCohnR1 k ℓ

/-- **Children of a generalized Cohn triple.** Let $k$ be a natural number, let $S$ be the integer
matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$, and let $(P, Q, R)$ be a $k$-generalized Cohn
triple associated with $(a, b, c)$. Then $(P, PQ - S, Q)$ is a $k$-generalized Cohn triple
associated with $(a, \lfloor (a^2 + kab + b^2)/c \rfloor, b)$, and $(Q, QR - S, R)$ is a
$k$-generalized Cohn triple associated with $(b, \lfloor (b^2 + kbc + c^2)/a \rfloor, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.5. -/
public theorem_wanted IsGenCohnTriple.step {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P (P * Q - genCohnS k) Q a ((a ^ 2 + k * a * b + b ^ 2) / c) b ∧
      IsGenCohnTriple k Q (Q * R - genCohnS k) R b ((b ^ 2 + k * b * c + c ^ 2) / a) c

/-- **A product identity for generalized Cohn matrices.** Let $k$ be a natural number, let $M$
be a $k$-generalized Cohn matrix, and let $E$ be the $2 \times 2$ integer matrix whose only
nonzero entry is $3 + 3k$, in row $2$ and column $1$. Then $MEM = (\operatorname{tr} M + k)M + E$
and $M^{-1} E M^{-1} = -(\operatorname{tr} M^{-1} + k)M^{-1} + E$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.7. -/
public theorem_wanted IsGenCohnMatrix.mul_E_mul {k : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : IsGenCohnMatrix k M) :
    M * !![0, 0; 3 + 3 * (k : ℤ), 0] * M =
        (M.trace + (k : ℤ)) • M + !![0, 0; 3 + 3 * (k : ℤ), 0] ∧
      M⁻¹ * !![0, 0; 3 + 3 * (k : ℤ), 0] * M⁻¹ =
        (-(M⁻¹.trace + (k : ℤ))) • M⁻¹ + !![0, 0; 3 + 3 * (k : ℤ), 0]

/-- **Vertices of the wide generalized Cohn tree are generalized Cohn triples.** Let $k$ be a
natural number. For every integer $\ell$ and every path $w$, the vertex of the wide
$k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$ at $w$ is a $k$-generalized Cohn triple
associated with the vertex of the wide $k$-generalized Markov tree $\mathrm{WMT}(k)$ at $w$.
Moreover, every $k$-generalized Markov triple $(a, b, c)$ with $a \le b$ and $c \le b$ has an
associated $k$-generalized Cohn triple.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.9. -/
public theorem_wanted wideGenCohnTree_isGenCohnTriple (k : ℕ) (ℓ : ℤ) :
    (∀ w, IsGenCohnTriple k (wideGenCohnTree k ℓ w).1 (wideGenCohnTree k ℓ w).2.1
      (wideGenCohnTree k ℓ w).2.2 (wideGenMarkovTree k w).1 (wideGenMarkovTree k w).2.1
      (wideGenMarkovTree k w).2.2) ∧
    ∀ a b c, IsGenMarkovTriple k a b c → a ≤ b → c ≤ b → ∃ P Q R, IsGenCohnTriple k P Q R a b c

/-- **Generalized Cohn triples with largest middle entry lie in wide generalized Cohn trees.**
Let $k$ be a natural number and let $(P, Q, R)$ be a $k$-generalized Cohn triple associated with
$(a, b, c)$, where $a \le b$ and $c \le b$. Then there are an integer $\ell$ and a path $w$ such
that $(P, Q, R)$ is the vertex of the wide $k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$
reached along $w$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.10. -/
public theorem_wanted IsGenCohnTriple.mem_wideGenCohnTree {k a b c : ℕ}
    {P Q R : Matrix (Fin 2) (Fin 2) ℤ} (h : IsGenCohnTriple k P Q R a b c) (hab : a ≤ b)
    (hcb : c ≤ b) : ∃ ℓ w, wideGenCohnTree k ℓ w = (P, Q, R)

/-- **Parent triples of a generalized Cohn triple.** Let $k$ be a natural number and let $S$ be
the integer matrix with rows $(k, 0)$ and $(3k^2 + 3k, k)$. Let $(P, Q, R)$ be a $k$-generalized
Cohn triple associated with $(a, b, c)$, and let $b' = \lfloor (a^2 + kac + c^2)/b \rfloor$. Then
$(P, R, P^{-1}(R + S))$ is a $k$-generalized Cohn triple associated with $(a, c, b')$, and
$((P + S)R^{-1}, P, R)$ is a $k$-generalized Cohn triple associated with $(b', a, c)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 3.11. -/
public theorem_wanted IsGenCohnTriple.parent {k a b c : ℕ} {P Q R : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsGenCohnTriple k P Q R a b c) :
    IsGenCohnTriple k P R (P⁻¹ * (R + genCohnS k)) a c ((a ^ 2 + k * a * c + c ^ 2) / b) ∧
      IsGenCohnTriple k ((P + genCohnS k) * R⁻¹) P R ((a ^ 2 + k * a * c + c ^ 2) / b) a c

/-- **Distinct paths give distinct middle matrices in the wide generalized Cohn tree.** For
every natural number $k$ and every integer $\ell$, if the vertices $(P, Q, R)$ and $(P', Q', R')$
of the wide $k$-generalized Cohn tree $\mathrm{WGCT}(k, \ell)$ at paths $w$ and $w'$ (finite
sequences of left and right steps) satisfy $Q = Q'$, then $w = w'$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Theorem 3.13. -/
public theorem_wanted wideGenCohnTree_snd_injective (k : ℕ) (ℓ : ℤ) :
    Function.Injective fun w => (wideGenCohnTree k ℓ w).2.1

/-- **Vertices of the generalized Cohn tree are Cohn triples over the Markov tree.** For every
natural number $k$, every integer $\ell$ and every path $w$ (a finite sequence of left and
right steps), the vertex $(P, Q, R)$ of the $k$-generalized Cohn tree $\mathrm{GCT}(k, \ell)$
at $w$ is a $k$-generalized Cohn triple associated with the vertex $(a, b, c)$ of the
$k$-generalized Markov tree $\mathrm{MT}(k)$ at the same path $w$.

The source phrases this as the canonical graph isomorphism
$\mathrm{GCT}(k, \ell) \to \mathrm{MT}(k)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.15. -/
public theorem_wanted genCohnTree_isGenCohnTriple (k : ℕ) (ℓ : ℤ) (w : List Bool) :
    IsGenCohnTriple k (genCohnTree k ℓ w).1 (genCohnTree k ℓ w).2.1 (genCohnTree k ℓ w).2.2
      (genMarkovTree k w).1 (genMarkovTree k w).2.1 (genMarkovTree k w).2.2

/-- **Middle matrices of the generalized Cohn tree are distinct.** For every natural number $k$
and every integer $\ell$, vertices of the $k$-generalized Cohn tree $\mathrm{GCT}(k, \ell)$ at
different paths have different middle matrices.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.16. -/
public theorem_wanted genCohnTree_snd_injective (k : ℕ) (ℓ : ℤ) :
    Function.Injective fun w => (genCohnTree k ℓ w).2.1

/-- **Cohn triples sit at a unique vertex of a Cohn tree.** Let $(P, Q, R)$ be a
$k$-generalized Cohn triple associated with $(a, b, c)$, where $b > \max\{a, c\}$. Then there is
exactly one pair $(\ell, w)$ of an integer $\ell$ and a path $w$ (a finite sequence of left and
right moves) such that $(P, Q, R)$ is the vertex of the $k$-generalized Cohn tree
$\mathrm{GCT}(k, \ell)$ reached along $w$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.17. -/
public theorem_wanted IsGenCohnTriple.existsUnique_mem_genCohnTree {k a b c : ℕ}
    {P Q R : Matrix (Fin 2) (Fin 2) ℤ} (h : IsGenCohnTriple k P Q R a b c) (hab : a < b)
    (hcb : c < b) : ∃! p : ℤ × List Bool, genCohnTree k p.1 p.2 = (P, Q, R)

/-- **The Farey tree.** Write a fraction $n/d$, with $n$ and $d$ natural numbers, for the pair
$(n, d)$, so that $1/0$ stands for $\infty$. The Farey tree $\mathrm{FT}$ is the infinite binary
tree of triples of fractions with root $(0/1, 1/1, 1/0)$ in which a vertex $(a/b, c/d, e/f)$
has left child $(a/b, (a+c)/(b+d), c/d)$ and right child $(c/d, (c+e)/(d+f), e/f)$. For a path
$w$, a finite sequence of left and right moves, this gives the vertex of $\mathrm{FT}$ reached
from the root by making the moves of $w$ in order.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def fareyTree (w : List Bool) : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) :=
  w.foldl (fun T d => match d, T with
    | false, (x, y, _) => (x, (x.1 + y.1, x.2 + y.2), y)
    | true, (_, y, z) => (y, (y.1 + z.1, y.2 + z.2), z)) ((0, 1), (1, 1), (1, 0))

/-- **Left child of the root of the Farey tree.** The left child of the root $(0/1, 1/1, 1/0)$
of the Farey tree is $(0/1, 1/2, 1/1)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem fareyTree_false : fareyTree [false] = ((0, 1), (1, 2), (1, 1)) := by
  decide

/-- **Farey triples.** Write a pair $(a, b)$ of natural numbers as the fraction $a/b$, so that
$1/0$ is allowed. Three such fractions $(a/b, c/d, e/f)$ form a Farey triple if
$\gcd(a, b) = \gcd(c, d) = \gcd(e, f) = 1$ and
$$|ad - bc| = |cf - de| = |eb - fa| = 1,$$
where the differences are taken in $\mathbb{Z}$.

The paper's printed condition writes $d/e$ for $e/f$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def IsFareyTriple (x y z : ℕ × ℕ) : Prop :=
  Nat.Coprime x.1 x.2 ∧ Nat.Coprime y.1 y.2 ∧ Nat.Coprime z.1 z.2 ∧
    |(x.1 : ℤ) * y.2 - x.2 * y.1| = 1 ∧ |(y.1 : ℤ) * z.2 - y.2 * z.1| = 1 ∧
    |(z.1 : ℤ) * x.2 - z.2 * x.1| = 1

/-- **The triple $(0/1, 1/1, 1/0)$ is a Farey triple.** The fractions $0/1$, $1/1$ and $1/0$,
given as the pairs of natural numbers $(0, 1)$, $(1, 1)$ and $(1, 0)$, form a Farey triple.

This triple is the root of the Farey tree.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public theorem isFareyTriple_root : IsFareyTriple (0, 1) (1, 1) (1, 0) := by
  unfold IsFareyTriple
  decide

/-- **Basic properties of the Farey tree.** Write a fraction $a/b$, with $a$ and $b$ natural
numbers, for the pair $(a, b)$, so that $1/0$ stands for $\infty$, and compare fractions by
cross multiplication: $a/b < c/d$ means $ad < cb$. (1) If $(a/b, c/d, e/f)$ is a Farey triple,
then so are $(a/b, (a+c)/(b+d), c/d)$ and $(c/d, (c+e)/(d+f), e/f)$; and the vertex of the
Farey tree reached along every path is a Farey triple. (2) For all coprime positive natural
numbers $a$ and $b$ there is exactly one path along which the vertex of the Farey tree has
second entry $a/b$. (3) Every vertex $(a/b, c/d, e/f)$ of the Farey tree satisfies
$a/b < c/d < e/f$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 3.22 (citing Aigner,
Section 3.2). -/
public theorem_wanted fareyTree_properties :
    (∀ x y z, IsFareyTriple x y z →
      IsFareyTriple x (x.1 + y.1, x.2 + y.2) y ∧ IsFareyTriple y (y.1 + z.1, y.2 + z.2) z) ∧
    (∀ w, IsFareyTriple (fareyTree w).1 (fareyTree w).2.1 (fareyTree w).2.2) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → ∃! w, (fareyTree w).2.1 = (a, b)) ∧
    ∀ w, (fareyTree w).1.1 * (fareyTree w).2.1.2 < (fareyTree w).2.1.1 * (fareyTree w).1.2 ∧
      (fareyTree w).2.1.1 * (fareyTree w).2.2.2 < (fareyTree w).2.2.1 * (fareyTree w).2.1.2

/-- **Fraction labels of generalized Cohn matrices.** Let $k$ be a natural number and $\ell$ an
integer, and write a pair $(a, b)$ of natural numbers as the fraction $a/b$. An integer
$2 \times 2$ matrix $C$ is labeled by the fraction $q$, written $C = C_q(k, \ell)$, if there is a
path $w$ from the root such that, for one of the three positions (first, second or third), $C$
is the entry in that position of the vertex of the generalized Cohn tree $\mathrm{GCT}(k, \ell)$
at $w$ and $q$ is the entry in that position of the vertex of the Farey tree at $w$.

The paper labels only second entries; here first and third entries carry the labels of the vertex
where they were created, which gives $C_{0/1}$ and $C_{1/0}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public def IsGenCohnLabel (k : ℕ) (ℓ : ℤ) (q : ℕ × ℕ) (C : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  ∃ w, ((fareyTree w).1 = q ∧ (genCohnTree k ℓ w).1 = C) ∨
    ((fareyTree w).2.1 = q ∧ (genCohnTree k ℓ w).2.1 = C) ∨
    ((fareyTree w).2.2 = q ∧ (genCohnTree k ℓ w).2.2 = C)

/-- **The middle matrix of the root of $\mathrm{GCT}(k, \ell)$ has label $1/1$.** For every
natural number $k$ and every integer $\ell$, the second entry of the root vertex of the
generalized Cohn tree $\mathrm{GCT}(k, \ell)$ is labeled by the fraction $1/1$, that is, it is
$C_{1/1}(k, \ell)$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2. -/
public theorem isGenCohnLabel_one (k : ℕ) (ℓ : ℤ) :
    IsGenCohnLabel k ℓ (1, 1) (genCohnTree k ℓ []).2.1 :=
  ⟨[], Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- **The Cohn labeling is injective and increasing.** Fix a natural number $k$ and an integer
$\ell$. Write fractions $a/b$, with $a$ and $b$ natural numbers, as pairs $(a, b)$, compared by
cross multiplication ($a/b < c/d$ means $ad < cb$), and write $C = C_q(k, \ell)$ when the
matrix $C$ carries the fraction label $q$ in the $k$-generalized Cohn tree $\mathrm{GCT}(k, \ell)$.
For an integer $2 \times 2$ matrix $M = (m_{ij})$ let $I_M = m_{11}/m_{12} \in \mathbb{Q}$.
(1) If $C = C_q(k, \ell)$ and $C = C_{q'}(k, \ell)$, then $q = q'$. (2) If $C = C_q(k, \ell)$,
$C' = C_{q'}(k, \ell)$ and $q < q'$, then $I_C < I_{C'}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 3.23. -/
public theorem_wanted genCohnLabel_injective_index_strictMono (k : ℕ) (ℓ : ℤ) :
    (∀ q q' C, IsGenCohnLabel k ℓ q C → IsGenCohnLabel k ℓ q' C → q = q') ∧
    ∀ q q' C C', IsGenCohnLabel k ℓ q C → IsGenCohnLabel k ℓ q' C' → q.1 * q'.2 < q'.1 * q.2 →
      (C 0 0 : ℚ) / C 0 1 < (C' 0 0 : ℚ) / C' 0 1

/-- **Fraction labeling of generalized Markov numbers.** Let $k$ be a natural number. Write a
fraction $n/d$ as the pair $(n, d)$ of natural numbers, with $1/0$ standing for $\infty$. Let
$FT$ be the Farey tree and $MT(k)$ the $k$-generalized Markov tree, with vertices of both
indexed by finite paths of left and right steps from the root. A natural number $m$ carries the
label $q$, written $m = m_q$, when there are a path $w$ and a position $i \in \{1, 2, 3\}$ such
that the $i$-th entry of the vertex of $FT$ at $w$ is $q$ and the $i$-th entry of the vertex of
$MT(k)$ at $w$ is $m$.

On fractions in $[0, 1]$ this gives $m_{0/1} = 1$, $m_{1/1} = k + 2$ and, for $t \in (0, 1)$,
the number $m_t$ of Gyoda and Maruyama.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public def IsGenMarkovLabel (k : ℕ) (q : ℕ × ℕ) (m : ℕ) : Prop :=
  ∃ w, ((fareyTree w).1 = q ∧ (genMarkovTree k w).1 = m) ∨
    ((fareyTree w).2.1 = q ∧ (genMarkovTree k w).2.1 = m) ∨
    ((fareyTree w).2.2 = q ∧ (genMarkovTree k w).2.2 = m)

/-- **The fraction $1/1$ labels $k + 2$.** For every natural number $k$, the number $k + 2$
carries the label $1/1$ in the fraction labeling of $k$-generalized Markov numbers, that is,
$m_{1/1} = k + 2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 4. -/
public theorem isGenMarkovLabel_one (k : ℕ) : IsGenMarkovLabel k (1, 1) (k + 2) :=
  ⟨[], Or.inr (Or.inl ⟨rfl, by rw [genMarkovTree_nil]⟩)⟩

/-- **Unique maximal triple via the fraction labeling.** Let $k$ be a natural number and $b$
a $k$-generalized Markov number. Then $b$ is the maximum of a unique $k$-generalized Markov
triple up to order if and only if there is exactly one pair $(n, d)$ of natural numbers with
$n \le d$ such that $b$ is a label of the fraction $n/d$ in the fraction labeling of
$k$-generalized Markov numbers.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 4.1. -/
public theorem_wanted hasUniqueMaxGenMarkovTriple_iff_existsUnique_label {k b : ℕ}
    (hb : IsGenMarkovNumber k b) :
    HasUniqueMaxGenMarkovTriple k b ↔ ∃! q : ℕ × ℕ, q.1 ≤ q.2 ∧ IsGenMarkovLabel k q b

/-- **Uniqueness of maximal triples and injectivity of the fraction labeling.** For every
natural number $k$, the following are equivalent: every $k$-generalized Markov number is the
maximum of a unique $k$-generalized Markov triple up to order (Conjecture 1.8 for $k$); and the
fraction labeling of $k$-generalized Markov numbers is injective on $[0, 1]$, that is, whenever
$(n, d)$ and $(n', d')$ are pairs of natural numbers with $n \le d$ and $n' \le d'$ and a number
$m$ is a label of both $n/d$ and $n'/d'$, then $(n, d) = (n', d')$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 4.2. -/
public theorem_wanted genMarkovUniqueness_iff_label_injective (k : ℕ) :
    (∀ b, IsGenMarkovNumber k b → HasUniqueMaxGenMarkovTriple k b) ↔
      ∀ q q' m, q.1 ≤ q.2 → q'.1 ≤ q'.2 → IsGenMarkovLabel k q m → IsGenMarkovLabel k q' m →
        q = q'

/-- **Characteristic number.** For natural numbers $m_r$, $m_t$, $m_s$, a natural number $x$ is
a characteristic number of $(m_r, m_t, m_s)$ when $0 < x < m_t/2$ and
$m_r x \equiv \pm m_s \pmod{m_t}$, that is, $m_t$ divides $m_r x - m_s$ or $m_r x + m_s$ in
$\mathbb{Z}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public def IsGenMarkovCharNumber (mr mt ms x : ℕ) : Prop :=
  0 < x ∧ 2 * x < mt ∧ ((mt : ℤ) ∣ mr * x - ms ∨ (mt : ℤ) ∣ mr * x + ms)

/-- **Characteristic number of $(1, 5, 2)$.** The number $2$ is a characteristic number of
$(m_r, m_t, m_s) = (1, 5, 2)$: indeed $0 < 2 < 5/2$ and $1 \cdot 2 \equiv 2 \pmod 5$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Definition 4.3. -/
public theorem isGenMarkovCharNumber_one_five_two : IsGenMarkovCharNumber 1 5 2 2 := by
  refine ⟨by norm_num, by norm_num, Or.inl ⟨0, by norm_num⟩⟩

/-- **Positive corner entry of the generalized Cohn tree for $\ell = -k$.** Let $k$ be a natural
number and $w$ a path, and suppose that the middle fraction $n/d$ of the vertex of the Farey
tree at $w$ satisfies $0 < n < d$. Then the $(1,1)$-entry of the middle matrix of the vertex of
the $k$-generalized Cohn tree $\mathrm{GCT}(k, -k)$ at $w$ is positive.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.4. -/
public theorem_wanted genCohnTree_neg_snd_entry_pos (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) :
    0 < (genCohnTree k (-k) w).2.1 0 0

/-- **Shape of the generalized Cohn matrices for $\ell = -k$.** Let $k$ be a natural number and
$w$ a path, and suppose that the middle fraction $n/d$ of the vertex of the Farey tree at $w$
satisfies $0 < n < d$. Let $(a, b, c)$ be the vertex of the $k$-generalized Markov tree
$\mathrm{MT}(k)$ at $w$, and let $C$ be the middle matrix of the vertex of the $k$-generalized
Cohn tree $\mathrm{GCT}(k, -k)$ at $w$. Then there is a natural number $u$ that is a
characteristic number of $(a, b, c)$ such that $C_{11} = u$, $C_{12} = b$ and
$C_{22} = (3 + 3k)b - u - k$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.5. -/
public theorem_wanted genCohnTree_neg_snd_eq (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) :
    ∃ u, IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
        (genMarkovTree k w).2.2 u ∧
      (genCohnTree k (-k) w).2.1 0 0 = u ∧
      (genCohnTree k (-k) w).2.1 0 1 = (genMarkovTree k w).2.1 ∧
      (genCohnTree k (-k) w).2.1 1 1 = (3 + 3 * k) * ((genMarkovTree k w).2.1 : ℤ) - u - k

/-- **The characteristic number solves $m_r x \equiv m_s \pmod{m_t}$.** Let $k \in \mathbb{N}$,
let $w$ be a finite sequence of left and right moves, let $(r, t, s)$ be the vertex of the
Farey tree at $w$, and let $(m_r, m_t, m_s)$ be the vertex of the $k$-generalized Markov tree
$\mathrm{MT}(k)$ at $w$. Write $t = n/d$. If $0 < n < d$ and $u$ is a characteristic number
of $(m_r, m_t, m_s)$, then $m_t$ divides $m_r u - m_s$ in $\mathbb{Z}$, that is,
$m_r u \equiv m_s \pmod{m_t}$.

Of the two congruences $m_r x \equiv \pm m_s \pmod{m_t}$ allowed in the definition of a
characteristic number, the one with the plus sign holds.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Corollary 4.6. -/
public theorem_wanted genMarkovCharNumber_dvd_sub (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    ((genMarkovTree k w).2.1 : ℤ) ∣ (genMarkovTree k w).1 * u - (genMarkovTree k w).2.2

/-- **The characteristic number solves $x^2 + kx + 1 \equiv 0 \pmod{m_t}$.** Let
$k \in \mathbb{N}$, let $w$ be a finite sequence of left and right moves, let $(r, t, s)$ be
the vertex of the Farey tree at $w$, and let $(m_r, m_t, m_s)$ be the vertex of the
$k$-generalized Markov tree $\mathrm{MT}(k)$ at $w$. Write $t = n/d$. If $0 < n < d$ and $u$
is a characteristic number of $(m_r, m_t, m_s)$, then $m_t$ divides $u^2 + ku + 1$, that is,
$u^2 + ku + 1 \equiv 0 \pmod{m_t}$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.7. -/
public theorem_wanted genMarkovCharNumber_sq_add (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    (genMarkovTree k w).2.1 ∣ u ^ 2 + k * u + 1

/-- **The characteristic number is less than $m_t/2 - k$.** Let $k \in \mathbb{N}$, let $w$ be a
finite sequence of left and right moves, let $(r, t, s)$ be the vertex of the Farey tree at $w$,
and let $(m_r, m_t, m_s)$ be the vertex of the $k$-generalized Markov tree $\mathrm{MT}(k)$ at
$w$. Write $t = n/d$. If $0 < n < d$ and $u$ is a characteristic number of $(m_r, m_t, m_s)$,
then $2(u + k) < m_t$, that is, $u + k < m_t/2$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Lemma 4.8. -/
public theorem_wanted genMarkovCharNumber_add_lt (k : ℕ) (w : List Bool)
    (ht : 0 < (fareyTree w).2.1.1) (ht1 : (fareyTree w).2.1.1 < (fareyTree w).2.1.2) (u : ℕ)
    (hu : IsGenMarkovCharNumber (genMarkovTree k w).1 (genMarkovTree k w).2.1
      (genMarkovTree k w).2.2 u) :
    2 * (u + k) < (genMarkovTree k w).2.1

end

end MetaMathlibExt
