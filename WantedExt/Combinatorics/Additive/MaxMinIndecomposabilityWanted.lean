/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Indecomposability over the max-min semiring

Statements from Benjamin Baily, Justine Dell, Henry L. Fleischmann, Faye Jackson, Ethan Pesikoff,
Steven J. Miller and Luke Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of
Integer Sequences 28 (2025), Article 25.2.7.

A polynomial or power series over the max-min semiring `(ℕ, max, min)` is recorded by its
coefficient sequence `ℕ → ℕ`. Addition is the pointwise maximum (`⊔` on functions) and the product
is the max-min convolution `(g ⊗ h)ₖ = max_{i + j = k} min(gᵢ, hⱼ)`. Lunar numbers in base `b`
are the polynomials with coefficients in `{0, …, b - 1}`; a lunar number with `n` digits is a
digit string `a : Fin n → Fin b` whose leading digit `a (n - 1)` is nonzero (degree `n - 1`).
Boolean polynomials are recorded by their supports `A ⊆ ℕ`: the product of two Boolean
polynomials has support the sumset `A + B`, and `|f|` is `A.card`.

The definitions follow the arXiv version of the paper (arXiv:2111.09786, titled *Irreducibility
Over the Max-Min Semiring*), where the JIS "indecomposable" is called "irreducible" and the JIS
`ℒ_b^n` is the set of degree-`n` polynomials of `ℬ_b[x]`. The quantitative statements of
Section 2 (Proposition 21 to Lemma 28) follow the JIS text, where `ℒ_b^n` is the set of lunar
numbers of degree at most `n`, recorded by digit strings `Fin (n + 1) → Fin b`. Proposition 20
(Hoeffding's inequality) is the proved `ProbabilityTheory.hoeffding_bernoulli_sum_abs_tail`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace MetaMathlibExt

@[expose] public section

open Pointwise Filter Topology

/-- **Max-min product.** The max-min product of sequences $g, h \colon \mathbb{N} \to \mathbb{N}$
is the sequence $g \otimes h$ with $(g \otimes h)_k = \max_{i + j = k} \min(g_i, h_j)$ for every
$k \in \mathbb{N}$, the maximum running over pairs of natural numbers $(i, j)$. This is the product
of the max-min semiring $(\mathbb{N}, \max, \min)$ on coefficient sequences.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public def maxMinMul (g h : ℕ → ℕ) : ℕ → ℕ :=
  fun k => (Finset.antidiagonal k).sup fun p => min (g p.1) (h p.2)

/-- **Constant coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_0 = \min(g_0, h_0)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_zero (g h : ℕ → ℕ) : maxMinMul g h 0 = min (g 0) (h 0) := by
  simp [maxMinMul]

/-- **Linear coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_1 = \max(\min(g_0, h_1), \min(g_1, h_0))$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_one (g h : ℕ → ℕ) :
    maxMinMul g h 1 = max (min (g 0) (h 1)) (min (g 1) (h 0)) := by
  simp [maxMinMul, Finset.Nat.antidiagonal_succ]

/-- **Monomials over the max-min semiring.** A coefficient sequence
$g : \mathbb{N} \to \mathbb{N}$ over the max-min semiring is a monomial when exactly one of its
entries is nonzero, that is, when it is $c x^i$ for some index $i$ and some coefficient $c \neq 0$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public def IsMaxMinMonomial (g : ℕ → ℕ) : Prop :=
  ∃ i, ∀ j, g j ≠ 0 ↔ j = i

/-- **The zero sequence is not a monomial.** The zero coefficient sequence
$\mathbb{N} \to \mathbb{N}$ is not a max-min monomial: a monomial has exactly one nonzero
entry, and the zero sequence has none.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinMonomial_zero : ¬ IsMaxMinMonomial 0 := by
  rintro ⟨i, hi⟩
  exact (hi i).2 rfl rfl

/-- **Max-min indecomposable sequences.** A coefficient sequence $f : \mathbb{N} \to \mathbb{N}$
is indecomposable (in the arXiv version: irreducible) when for all sequences
$g, h : \mathbb{N} \to \mathbb{N}$ with $g \otimes h = f$, where $\otimes$ is the max-min product,
$g$ or $h$ is a max-min monomial, that is, a sequence with exactly one nonzero term.

Factors range over all sequences $\mathbb{N} \to \mathbb{N}$; for a natural number $b$ and $f$
with all terms less than $b$, this is equivalent to factoring over $\{0, \dots, b - 1\}$, by
applying the digit map $x \mapsto \min(x, b - 1)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public def IsMaxMinIndecomposable (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, maxMinMul g h = f → IsMaxMinMonomial g ∨ IsMaxMinMonomial h

/-- **The zero sequence is decomposable.** The zero coefficient sequence
$\mathbb{N} \to \mathbb{N}$ is not indecomposable over the max-min semiring: it factors as
$0 = 0 \otimes 0$, where $\otimes$ is the max-min product, and the zero sequence is not a
monomial.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(definition of indecomposable). -/
public theorem not_isMaxMinIndecomposable_zero : ¬ IsMaxMinIndecomposable 0 := by
  intro h
  have h0 : maxMinMul (0 : ℕ → ℕ) 0 = 0 := by
    funext k
    simp [maxMinMul]
  rcases h 0 0 h0 with h1 | h1 <;> exact not_isMaxMinMonomial_zero h1

/-- **Coefficient sequence of a digit string.** Let $n$ and $b$ be natural numbers. The
coefficient sequence of a digit string $a = (a_0, \dots, a_{n-1})$ with digits in
$\{0, \dots, b - 1\}$ is the sequence $\mathbb{N} \to \mathbb{N}$ whose $k$-th term is $a_k$ for
$k < n$ and $0$ for $k \ge n$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public def digitSeq {n b : ℕ} (a : Fin n → Fin b) : ℕ → ℕ :=
  fun k => if hk : k < n then (a ⟨k, hk⟩ : ℕ) else 0

/-- **A digit string has no coefficients beyond its length.** Let $n$ and $b$ be natural numbers
and let $a = (a_0, \dots, a_{n-1})$ be a digit string with digits in $\{0, \dots, b - 1\}$. Then
for every $k \ge n$, the $k$-th term of the coefficient sequence of $a$ is $0$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(lunar numbers `ℒ_b` as polynomials over `ℬ_b = {0, …, b - 1}`). -/
public theorem digitSeq_of_le {n b : ℕ} (a : Fin n → Fin b) {k : ℕ} (hk : n ≤ k) :
    digitSeq a k = 0 := by
  simp [digitSeq, Nat.not_lt.2 hk]

/-- **Lunar unit.** For a natural number $b$, the lunar unit of base $b$ is the coefficient sequence
$\mathbb{N} \to \mathbb{N}$ whose constant term is $b - 1$ and whose other terms are all $0$, that
is, the constant polynomial $b - 1$ over the max-min semiring. The subtraction is truncated, so
the lunar unit of base $0$ is the zero sequence.

For sequences with all terms less than $b$, the lunar unit is the identity of the max-min product.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public def lunarUnit (b : ℕ) : ℕ → ℕ :=
  fun k => if k = 0 then b - 1 else 0

/-- **The lunar unit is a monomial.** For every natural number $b \ge 2$, the lunar unit of base
$b$, the sequence with constant term $b - 1$ and all other terms $0$, is a max-min monomial: it
has exactly one nonzero term.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public theorem isMaxMinMonomial_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsMaxMinMonomial (lunarUnit b) :=
  ⟨0, fun j => by by_cases hj : j = 0 <;> simp [lunarUnit, hj]; omega⟩

/-- **Lunar primes.** Let $b$ be a natural number. The lunar unit of base $b$ is the constant
polynomial $b - 1$, the sequence with constant term $b - 1$ and all other terms $0$. A coefficient
sequence $f : \mathbb{N} \to \mathbb{N}$ is a lunar prime of base $b$ (Applegate, LeBrun and
Sloane) when for all sequences $g, h : \mathbb{N} \to \mathbb{N}$ with all terms less than $b$ and
$g \otimes h = f$, where $\otimes$ is the max-min product, $g$ or $h$ is the lunar unit.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public def IsLunarPrime (b : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ g h : ℕ → ℕ, (∀ i, g i < b) → (∀ i, h i < b) → maxMinMul g h = f →
    g = lunarUnit b ∨ h = lunarUnit b

/-- **Zero is not a lunar prime.** For every integer $b \ge 2$, the zero sequence is not a lunar
prime of base $b$: $0 = 0 \otimes 0$, where $\otimes$ is the max-min product, and $0$ is not the
lunar unit, the constant polynomial $b - 1$ with coefficient sequence $(b - 1, 0, 0, \dots)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime lunar numbers). -/
public theorem not_isLunarPrime_zero {b : ℕ} (hb : 2 ≤ b) : ¬ IsLunarPrime b 0 := by
  intro h
  have h0 : maxMinMul (0 : ℕ → ℕ) 0 = 0 := by
    funext k
    simp [maxMinMul]
  have hne : (0 : ℕ → ℕ) ≠ lunarUnit b := by
    intro he
    have := congrFun he 0
    simp [lunarUnit] at this
    omega
  rcases h 0 0 (fun _ => by simp; omega) (fun _ => by simp; omega) h0 with h1 | h1 <;>
    exact hne h1

/-- **Lunar prime candidates.** Let $b$ be a natural number. A coefficient sequence
$f : \mathbb{N} \to \mathbb{N}$ is a prime candidate in base $b$ when its constant term $f_0$ is
nonzero and some term $f_i$ equals $b - 1$, where the subtraction is truncated, so that
$b - 1 = 0$ when $b = 0$. For $f$ with all terms less than $b$, the second condition says that
the largest coefficient of $f$ is $b - 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public def IsLunarPrimeCandidate (b : ℕ) (f : ℕ → ℕ) : Prop :=
  f 0 ≠ 0 ∧ ∃ i, f i = b - 1

/-- **The lunar unit is a prime candidate.** For every natural number $b \ge 2$, the lunar unit
of base $b$, the sequence with constant term $b - 1$ and all other terms $0$, is a prime candidate
in base $b$: its constant term is nonzero and one of its terms equals $b - 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 2
(definition of prime candidate). -/
public theorem isLunarPrimeCandidate_lunarUnit {b : ℕ} (hb : 2 ≤ b) :
    IsLunarPrimeCandidate b (lunarUnit b) :=
  ⟨by simp [lunarUnit]; omega, 0, by simp [lunarUnit]⟩

/-- **Shitov's theorem: almost all Boolean polynomials with nonzero constant term are prime.**
For $n \in \mathbb{N}$, consider the Boolean polynomials of degree exactly $n$ with nonzero
constant term, that is, the base-$2$ lunar numbers given by digit strings
$(a_0, \dots, a_n) \in \{0, 1\}^{n+1}$ with $a_0 \ne 0$ and $a_n \ne 0$. The proportion of
these which are lunar primes in base $2$ tends to $1$ as $n \to \infty$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 10
(`jis-2025-25.2.7-thm-10`), quoting Shitov (2014), Theorem 2.5. -/
public theorem_wanted shitov_boolean_prime_density :
    Tendsto (fun n : ℕ =>
      ({a : Fin (n + 1) → Fin 2 | digitSeq a n ≠ 0 ∧ digitSeq a 0 ≠ 0 ∧
          IsLunarPrime 2 (digitSeq a)}.ncard : ℝ) /
        ({a : Fin (n + 1) → Fin 2 | digitSeq a n ≠ 0 ∧ digitSeq a 0 ≠ 0}.ncard : ℝ))
      atTop (𝓝 1)

/-- **Almost all max-min polynomials are indecomposable.** Fix an integer $b \ge 2$. For each
$n$, among the polynomials of degree $n$ with coefficients in $\mathcal{B}_b = \{0, \dots, b - 1\}$,
that is, coefficient strings $(a_0, \dots, a_n)$ with $a_n \ne 0$, the proportion of those that
are indecomposable over the max-min semiring tends to $1$ as $n \to \infty$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 11
(`jis-2025-25.2.7-thm-11`). -/
public theorem_wanted maxMin_indecomposable_density {b : ℕ} (hb : 2 ≤ b) :
    Tendsto (fun n : ℕ =>
      ({a : Fin (n + 1) → Fin b | digitSeq a n ≠ 0 ∧ IsMaxMinIndecomposable (digitSeq a)}.ncard
          : ℝ) /
        ({a : Fin (n + 1) → Fin b | digitSeq a n ≠ 0}.ncard : ℝ))
      atTop (𝓝 1)

/-- **Asymptotic count of lunar primes.** Fix an integer $b \ge 2$. For $n \ge 1$ let $\pi_b(n)$
be the number of digit strings $(a_0, \dots, a_{n-1})$ with $a_k \in \{0, \dots, b - 1\}$ and
leading digit $a_{n-1} \ne 0$ whose coefficient sequence $(a_0, \dots, a_{n-1}, 0, 0, \dots)$ is a
lunar prime of base $b$; these are the prime lunar numbers of base $b$ with $n$ digits. Then
$\pi_b(n) \sim (b - 1)^2 b^{n-2}$ as $n \to \infty$, as conjectured by Applegate, LeBrun and
Sloane.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Corollary 12
(`jis-2025-25.2.7-cor-12`). -/
public theorem_wanted lunar_prime_count_isEquivalent {b : ℕ} (hb : 2 ≤ b) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ =>
        ({a : Fin n → Fin b | digitSeq a (n - 1) ≠ 0 ∧ IsLunarPrime b (digitSeq a)}.ncard : ℝ))
      (fun n : ℕ => ((b : ℝ) - 1) ^ 2 * (b : ℝ) ^ n / (b : ℝ) ^ 2)

/-- **Monotone digit maps are lunar homomorphisms.** Let $d : \mathbb{N} \to \mathbb{N}$ be
nondecreasing, and for a coefficient sequence $f : \mathbb{N} \to \mathbb{N}$ write $d(f)$ for the
sequence $k \mapsto d(f_k)$. Write $f \oplus g$ for the pointwise maximum and $f \otimes g$ for the
max-min product of coefficient sequences $f$ and $g$. Then for all $f$ and $g$,
$d(f) \oplus d(g) = d(f \oplus g)$ and $d(f) \otimes d(g) = d(f \otimes g)$.

This is Theorem 15 (Applegate, LeBrun and Sloane, prime promotion), stated for every nondecreasing
map on $\mathbb{N}$; a base-$b$ digit map, a nondecreasing map on the digits, extends to such a map.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 15
(`jis-2025-25.2.7-thm-15`). -/
public theorem_wanted digitMap_lunar_hom {d : ℕ → ℕ} (hd : Monotone d) (f g : ℕ → ℕ) :
    (d ∘ f) ⊔ (d ∘ g) = d ∘ (f ⊔ g) ∧ maxMinMul (d ∘ f) (d ∘ g) = d ∘ maxMinMul f g

/-- **Counting Boolean factor pairs with a small sumset.** Let $n$ and $k$ be natural numbers with
$0 < k \le n$, and let $d > 0$ be a real number. Then the number of pairs $(A, B)$ of finite sets
of natural numbers such that $0 \in A$, the largest element of $A$ is $k$, the largest element of
$B$ is $n - k$, and $|A + B| \le |A| + |B| + d$, where $A + B = \{a + b : a \in A, b \in B\}$ is
the sumset, is at most $n^{2d+2} 2^k$.

This is Lemma 19 for Boolean polynomials $f$ and $g$ recorded by their supports $A$ and $B$: the
conditions say that $f$ has nonzero constant term, $\deg f = k$ and $\deg g = n - k$, and the
support of their max-min product $f \otimes g$ is $A + B$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 19
(`jis-2025-25.2.7-lem-19`). -/
public theorem_wanted boolean_close_factor_pairs_card_le {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {d : ℝ} (hd : 0 < d) :
    ({p : Finset ℕ × Finset ℕ | 0 ∈ p.1 ∧ k ∈ p.1 ∧ (∀ x ∈ p.1, x ≤ k) ∧
        n - k ∈ p.2 ∧ (∀ y ∈ p.2, y ≤ n - k) ∧
        ((p.1 + p.2).card : ℝ) ≤ p.1.card + p.2.card + d}.ncard : ℝ) ≤
      (n : ℝ) ^ (2 * d + 2) * 2 ^ k

/-- **Indecomposable prime candidates are lunar primes.** Let $n$ and $b \ge 2$ be natural
numbers, let $a = (a_0, \dots, a_{n-1})$ be a digit string with digits in $\{0, \dots, b - 1\}$,
and let $f$ be its coefficient sequence. If $f$ is a prime candidate in base $b$ and $f$ is
max-min indecomposable, then $f$ is a lunar prime of base $b$.

This is Lemma 30 (Applegate, LeBrun and Sloane).

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Lemma 30
(`jis-2025-25.2.7-lem-30`). -/
public theorem_wanted isLunarPrime_of_indecomposable_candidate {n b : ℕ} (hb : 2 ≤ b)
    (a : Fin n → Fin b) (hc : IsLunarPrimeCandidate b (digitSeq a))
    (hi : IsMaxMinIndecomposable (digitSeq a)) :
    IsLunarPrime b (digitSeq a)


/-- **Level counts of a lunar number.** Let $f$ be a lunar number of base $b$ and degree at most
$n$, with digits $c_0, \dots, c_n \in \{0, \dots, b - 1\}$, and let $i$ be a natural number. The
level count $|f_i|$ is the number of indices $k \le n$ with $c_k \ge i$, that is, the number of
nonzero coefficients of the $i$-level support $f_i = s_i(f)$, the Boolean polynomial with
coefficient $1$ at $x^k$ when $c_k \ge i$ and $0$ otherwise.

A lunar number $f$ is not a monomial $t x^m$ (with $t = 0$ allowed) if and only if $|f_1| \ge 2$,
and $f_i$ is not a monomial if and only if $|f_i| \ge 2$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, Definitions 13 and 16. -/
public def lunarLevelCount {n b : ℕ} (i : ℕ) (f : Fin (n + 1) → Fin b) : ℕ :=
  (Finset.univ.filter fun k => i ≤ (f k : ℕ)).card

/-- **Level counts of $1 \oplus 2x^2$ in base $3$.** For the base-$3$ lunar number
$f = 1 \oplus 2x^2$ of degree at most $2$, with digits $1, 0, 2$, exactly two digits are at least
$1$ and exactly one digit is at least $2$: $|f_1| = 2$ and $|f_2| = 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, Definitions 13 and 16. -/
public theorem lunarLevelCount_example :
    lunarLevelCount 1 (![1, 0, 2] : Fin 3 → Fin 3) = 2 ∧
      lunarLevelCount 2 (![1, 0, 2] : Fin 3 → Fin 3) = 1 := by
  decide

/-- **Decomposable lunar numbers.** For natural numbers $b$ and $n$, let $\mathcal{L}_b^n$ be the
set of lunar numbers of base $b$ and degree at most $n$, that is, polynomials
$c_0 \oplus c_1 x \oplus \dots \oplus c_n x^n$ with digits $c_k \in \{0, \dots, b - 1\}$. The set
$\Sigma_b^n$ of decomposable lunar numbers consists of the $h \in \mathcal{L}_b^n$ that factor as
$h = f \otimes g$ under the max-min product, with $f, g \in \mathcal{L}_b^n$ each having at least
two nonzero digits.

A monomial is $t x^m$ with $t \in \{0, \dots, b - 1\}$, so the factors are exactly the
non-monomials. Every factor of a nonzero lunar number of degree at most $n$ lies in
$\mathcal{L}_b^n$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Proposition 21. -/
public def lunarDecomposableSet (b n : ℕ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount 1 f ∧ 2 ≤ lunarLevelCount 1 g ∧
    maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}

/-- **Level-decomposable lunar numbers.** Let $b$ and $n$ be natural numbers and
$a = \lfloor b/2 \rfloor$. For a lunar number $f$ of base $b$ and degree at most $n$, given by its
digits $f_0, \dots, f_n \in \{0, \dots, b - 1\}$, write $|f_a|$ for the number of indices $k \le n$
with $f_k \ge a$. The set $\mathcal{D}_b^n$ consists of the lunar numbers $h$ of base $b$ and
degree at most $n$ such that $h = f \otimes g$ for some lunar numbers $f$ and $g$ of base $b$ and
degree at most $n$ with $|f_a| \ge 2$ and $|g_a| \ge 2$, where $\otimes$ is the max-min product of
coefficient sequences.

For $b \ge 2$ we have $a \ge 1$, so $|f_a| \ge 2$ implies that $f$ has at least two nonzero
digits; hence $\mathcal{D}_b^n$ is contained in the set $\Sigma_b^n$ of decomposable lunar numbers
of degree at most $n$, and one writes $\mathcal{I}_b^n = \Sigma_b^n \setminus \mathcal{D}_b^n$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Remark 22. -/
public def lunarLevelDecomposableSet (b n : ℕ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount (b / 2) f ∧
    2 ≤ lunarLevelCount (b / 2) g ∧ maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}

/-- **Hoeffding extremal lunar numbers.** Let $b$ and $n$ be natural numbers and $d$ a real
number. Let $\mathcal{L}_b^n$ be the set of lunar numbers of base $b$ and degree at most $n$
(digit strings $c_0, \dots, c_n$ with digits in $\{0, \dots, b - 1\}$), with the max-min product
$\otimes$, and for $f \in \mathcal{L}_b^n$ let $|f_i|$ be the number of its digits that are at
least $i$. The set $\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers consists of the
$h \in \mathcal{L}_b^n$ for which there is an index $i$ with $1 \le i \le b - 1$ such that either
$\bigl||h_i| - (b - i)n/b\bigr| > d/2$, or $h = f \otimes g$ for some $f, g \in \mathcal{L}_b^n$
with $\bigl||f_i| + |g_i| - (b - i)(n + 1)/b\bigr| > d/2$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Definition 23. -/
public def lunarHoeffdingExtremalSet (b n : ℕ) (d : ℝ) : Set (Fin (n + 1) → Fin b) :=
  {h | ∃ i, 1 ≤ i ∧ i ≤ b - 1 ∧
    (d / 2 < |(lunarLevelCount i h : ℝ) - ((b : ℝ) - i) * n / b| ∨
      ∃ f g : Fin (n + 1) → Fin b, maxMinMul (digitSeq f) (digitSeq g) = digitSeq h ∧
        d / 2 < |((lunarLevelCount i f + lunarLevelCount i g : ℕ) : ℝ) -
          ((b : ℝ) - i) * (n + 1) / b|)}

private theorem digitSeq_one_one_zero_mul :
    maxMinMul (digitSeq (![1, 1, 0] : Fin 3 → Fin 2)) (digitSeq (![1, 1, 0] : Fin 3 → Fin 2)) =
      digitSeq (![1, 1, 1] : Fin 3 → Fin 2) := by
  funext k
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · have h1 : digitSeq (![1, 1, 1] : Fin 3 → Fin 2) (k + 3) = 0 := digitSeq_of_le _ (by omega)
    rw [h1, maxMinMul]
    refine le_antisymm (Finset.sup_le fun p hp => ?_) (Nat.zero_le _)
    rw [Finset.mem_antidiagonal] at hp
    have : 2 ≤ p.1 ∨ 2 ≤ p.2 := by omega
    rcases this with h | h
    · have : digitSeq (![1, 1, 0] : Fin 3 → Fin 2) p.1 = 0 := by
        rcases Nat.lt_or_ge p.1 3 with h3 | h3
        · rw [show p.1 = 2 by omega]
          decide
        · exact digitSeq_of_le _ h3
      simp [this]
    · have : digitSeq (![1, 1, 0] : Fin 3 → Fin 2) p.2 = 0 := by
        rcases Nat.lt_or_ge p.2 3 with h3 | h3
        · rw [show p.2 = 2 by omega]
          decide
        · exact digitSeq_of_le _ h3
      simp [this]

/-- **A decomposable lunar number in base 2.** In base $2$, the lunar number with digit string
$(1, 1, 1)$, that is $1 \oplus x \oplus x^2$ with $\oplus$ the lunar sum (digitwise maximum), lies
both in the set $\Sigma_2^2$ of decomposable lunar numbers of degree at most $2$ and in the set
$\mathcal{D}_2^2$ of level-decomposable lunar numbers of degree at most $2$.

A factorization witnessing both is $1 \oplus x \oplus x^2 = (1 \oplus x) \otimes (1 \oplus x)$,
where $\otimes$ is the max-min product and $1 \oplus x$ has digit string $(1, 1, 0)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Section 2, before Proposition 21 and Remark 22. -/
public theorem mem_lunarDecomposableSet_example :
    (![1, 1, 1] : Fin 3 → Fin 2) ∈ lunarDecomposableSet 2 2 ∧
      (![1, 1, 1] : Fin 3 → Fin 2) ∈ lunarLevelDecomposableSet 2 2 :=
  ⟨⟨![1, 1, 0], ![1, 1, 0], by decide, by decide, digitSeq_one_one_zero_mul⟩,
    ⟨![1, 1, 0], ![1, 1, 0], by decide, by decide, digitSeq_one_one_zero_mul⟩⟩

/-- **An example of a Hoeffding extremal lunar number.** In base $2$, the zero lunar number of
degree at most $2$ (the digit string $(0, 0, 0)$) lies in the $1$-Hoeffding extremal set
$\mathcal{H}_2^2(1)$: for the level $i = 1$, the number $|0_1|$ of its digits that are at least
$1$ is $0$, and $\left|0 - (2 - 1) \cdot 2 / 2\right| = 1 > 1/2$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Definition 23. -/
public theorem zero_mem_lunarHoeffdingExtremalSet :
    (0 : Fin 3 → Fin 2) ∈ lunarHoeffdingExtremalSet 2 2 1 := by
  refine ⟨1, le_rfl, le_rfl, Or.inl ?_⟩
  have : lunarLevelCount 1 (0 : Fin 3 → Fin 2) = 0 := by decide
  rw [this]
  norm_num

/-- **Upper bound on the number of decomposable lunar numbers.** Fix an integer $b \ge 2$. There
is a constant $C > 0$ such that for every integer $n \ge 2$ and all reals $d > 0$ and $v > 0$, the
set $\Sigma_b^n$ of decomposable lunar numbers of base $b$ and degree at most $n$ satisfies
$$|\Sigma_b^n| \le C b^{n+1} \Big(n^2 e^{-d^2/(4(n+2))} + n^{2d+4} 2^{d/2-(n+1)/3} +
v n^{2d+2} 2^v b^{d/2-n/b} + n^2 2^{-v}\Big).$$

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Proposition 21 (`jis-2025-25.2.7-prop-21`). -/
public theorem_wanted lunarDecomposableSet_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ d v : ℝ, 0 < d → 0 < v →
      ((lunarDecomposableSet b n).ncard : ℝ) ≤ C * (b : ℝ) ^ (n + 1) *
        ((n : ℝ) ^ 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) +
          (n : ℝ) ^ (2 * d + 4) * (2 : ℝ) ^ (d / 2 - (n + 1) / 3) +
          v * (n : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ v * (b : ℝ) ^ (d / 2 - n / b) +
          (n : ℝ) ^ 2 * (2 : ℝ) ^ (-v))

/-- **Bound on the number of Hoeffding extremal lunar numbers.** Fix an integer $b \ge 2$. There is
a constant $C > 0$ such that for every integer $n \ge 1$ and every real $d > 0$, the set
$\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers of base $b$ and degree at most $n$
has at most $C n^2 e^{-d^2/(4(n+2))} b^n$ elements.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 24 (`jis-2025-25.2.7-lem-24`). -/
public theorem_wanted lunarHoeffdingExtremalSet_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ d : ℝ, 0 < d →
      ((lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
        C * (n : ℝ) ^ 2 * Real.exp (-d ^ 2 / (4 * (n + 2))) * (b : ℝ) ^ n

/-- **Level counts of a product that is not Hoeffding extremal.** Let $b$ and $n$ be natural
numbers, $d$ a real number and $f, g, h$ lunar numbers of base $b$ and degree at most $n$ with
$h = f \otimes g$ under the max-min product. For a natural number $i$ write $|f_i|$, $|g_i|$ and
$|h_i|$ for the numbers of digits of $f$, $g$ and $h$ that are at least $i$. If $h$ is not in the
set $\mathcal{H}_b^n(d)$ of $d$-Hoeffding extremal lunar numbers of base $b$ and degree at most
$n$, then $|h_i| \le |f_i| + |g_i| + d$ for every $i$ with $1 \le i \le b - 1$.

The source also assumes that $h$ lies in the set $\Sigma_b^n$ of decomposable lunar numbers of
base $b$ and degree at most $n$, which is not needed, and prints $|b_i|$ for $|g_i|$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 25 (`jis-2025-25.2.7-lem-25`). -/
public theorem_wanted lunarLevelCount_le_of_not_mem_lunarHoeffdingExtremalSet {b n : ℕ} {d : ℝ}
    {f g h : Fin (n + 1) → Fin b} (hfg : maxMinMul (digitSeq f) (digitSeq g) = digitSeq h)
    (hH : h ∉ lunarHoeffdingExtremalSet b n d) {i : ℕ} (hi : 1 ≤ i) (hib : i ≤ b - 1) :
    (lunarLevelCount i h : ℝ) ≤ lunarLevelCount i f + lunarLevelCount i g + d

/-- **Bound on level-decomposable lunar numbers that are not Hoeffding extremal.** Let $b \ge 2$
and $n$ be natural numbers and $d > 0$ a real number. The number of elements of
$\mathcal{D}_b^n \setminus \mathcal{H}_b^n(d)$ is at most $n^{2d+4} 2^{d/2-n/3} b^{n+1}$, where
$\mathcal{D}_b^n$ is the set of level-decomposable lunar numbers of base $b$ and degree at most
$n$ and $\mathcal{H}_b^n(d)$ is the set of $d$-Hoeffding extremal ones.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 26 (`jis-2025-25.2.7-lem-26`). -/
public theorem_wanted lunarLevelDecomposableSet_diff_ncard_le {b : ℕ} (hb : 2 ≤ b) (n : ℕ)
    {d : ℝ} (hd : 0 < d) :
    ((lunarLevelDecomposableSet b n \ lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
      (n : ℝ) ^ (2 * d + 4) * (2 : ℝ) ^ (d / 2 - n / 3) * (b : ℝ) ^ (n + 1)

/-- **Decomposable lunar numbers with a low-degree factor.** Let $b \ge 2$ and $n$ be natural
numbers and let $d > 0$ and $v > 0$ be reals. Count the lunar numbers $h$ of base $b$ and degree at
most $n$ that lie in $\Sigma_b^n \setminus \mathcal{H}_b^n(d)$ (decomposable but not $d$-Hoeffding
extremal) and can be written as $h = f \otimes g$, with $\otimes$ the max-min product, where $f$
and $g$ are lunar numbers of base $b$ and degree at most $n$, each with at least two nonzero
digits, and every digit $f_k$ with $k > v$ is zero. Their number is at most
$v \, n^{2d+3} \, 2^v \, (b - 1)^{(b-1)n/b + d/2}$.

The factorization is required to be nontrivial, as in the source's proof; if trivial
factorizations $h = (b - 1) \otimes h$ counted, the claim would fail at $b = 2$, $n = 2$, $d = 5$,
$v = 10^{-4}$: the lunar number with digit string $(1, 1, 1)$, that is $1 \oplus x \oplus x^2$
with $\oplus$ the lunar sum (digitwise maximum), lies in $\Sigma_2^2 \setminus \mathcal{H}_2^2(5)$,
but the bound is $8192 \cdot 10^{-4} \cdot 2^{10^{-4}} < 1$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 27 (`jis-2025-25.2.7-lem-27`). -/
public theorem_wanted lunar_low_degree_factor_ncard_le {b : ℕ} (hb : 2 ≤ b) (n : ℕ) {d v : ℝ}
    (hd : 0 < d) (hv : 0 < v) :
    ({h | h ∈ lunarDecomposableSet b n \ lunarHoeffdingExtremalSet b n d ∧
        ∃ f g : Fin (n + 1) → Fin b, 2 ≤ lunarLevelCount 1 f ∧ 2 ≤ lunarLevelCount 1 g ∧
          (∀ k : Fin (n + 1), v < (k : ℝ) → (f k : ℕ) = 0) ∧
          maxMinMul (digitSeq f) (digitSeq g) = digitSeq h}.ncard : ℝ) ≤
      v * (n : ℝ) ^ (2 * d + 3) * (2 : ℝ) ^ v * ((b : ℝ) - 1) ^ (((b : ℝ) - 1) * n / b + d / 2)

/-- **Bound on decomposable lunar numbers neither level decomposable nor extremal.** Fix an integer
$b \ge 2$. For a natural number $n$ let $\mathcal{I}_b^n = \Sigma_b^n \setminus \mathcal{D}_b^n$,
where $\Sigma_b^n$ is the set of decomposable lunar numbers of base $b$ and degree at most $n$ and
$\mathcal{D}_b^n$ the set of level-decomposable ones, and for a real $d$ let $\mathcal{H}_b^n(d)$
be the set of $d$-Hoeffding extremal ones. There is a constant $C > 0$ such that for every natural
number $n$ and all reals $d > 0$ and $v > 0$,
$$|\mathcal{I}_b^n \setminus \mathcal{H}_b^n(d)| \le
C \Big(v n^{2d+2} 2^v b^{(b-1)n/b + d/2} + n^2 2^{-v} b^{n+1}\Big).$$

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7,
Lemma 28 (`jis-2025-25.2.7-lem-28`). -/
public theorem_wanted lunarIndecomposableLevel_diff_ncard_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ d v : ℝ, 0 < d → 0 < v →
      (((lunarDecomposableSet b n \ lunarLevelDecomposableSet b n) \
          lunarHoeffdingExtremalSet b n d).ncard : ℝ) ≤
        C * (v * (n : ℝ) ^ (2 * d + 2) * (2 : ℝ) ^ v *
            (b : ℝ) ^ (((b : ℝ) - 1) * n / b + d / 2) +
          (n : ℝ) ^ 2 * (2 : ℝ) ^ (-v) * (b : ℝ) ^ (n + 1))

end

end MetaMathlibExt
