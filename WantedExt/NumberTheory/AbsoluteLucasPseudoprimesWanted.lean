/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.Algebra.Polynomial.PrimeValueConditions
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace MetaMathlibExt

@[expose] public section

/-- **Jacobi symbols of a discriminant $D$ agree at odd primes congruent modulo $D$.** Let $p$ and
$p'$ be odd primes and let $D$ be an integer with $D \equiv 0$ or $1 \pmod 4$ that is coprime to
$p$. If $p' = p + D x$ for some integer $x$, then the Jacobi symbols agree:
$\left(\frac{D}{p'}\right) = \left(\frac{D}{p}\right)$.

For an odd prime $p$ the Jacobi symbol $\left(\frac{D}{p}\right)$ is the Legendre symbol and agrees
with the Kronecker symbol.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 1 (`integers-2026-A102-lem-1`). -/
public theorem_wanted jacobiSym_prime_add_mul_eq {p p' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp' : p'.Prime) (hp'2 : p' ≠ 2) {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1)
    (hDp : IsCoprime D p) {x : ℤ} (hx : (p' : ℤ) = p + D * x) :
    jacobiSym D p' = jacobiSym D p

/-- **Ballot's Lemma 2: three divisibilities as one congruence.** Let
$\varepsilon_1, \varepsilon_2, \varepsilon_3 \in \{1, -1\}$, let $c_1, c_2, c_3$ be pairwise coprime
positive integers, let $g \ne 0$ be an integer, and put
$n = (c_1 g + \varepsilon_1)(c_2 g + \varepsilon_2)(c_3 g + \varepsilon_3)$ and
$\varepsilon_n = \varepsilon_1 \varepsilon_2 \varepsilon_3$. Then $c_i g \mid n - \varepsilon_n$ for
$i = 1, 2, 3$ if and only if
$$c_1 c_2 c_3 \mid g (\varepsilon_3 c_1 c_2 + \varepsilon_2 c_1 c_3 + \varepsilon_1 c_2 c_3) +
\varepsilon_n (\varepsilon_1 c_1 + \varepsilon_2 c_2 + \varepsilon_3 c_3).$$

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 2 (`integers-2026-A102-lem-2`). -/
public theorem_wanted mul_dvd_prod_sub_sign_iff {ε₁ ε₂ ε₃ c₁ c₂ c₃ g : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁₂ : IsCoprime c₁ c₂) (h₁₃ : IsCoprime c₁ c₃) (h₂₃ : IsCoprime c₂ c₃) (hg : g ≠ 0) :
    (c₁ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃ ∧
      c₂ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃ ∧
      c₃ * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃) ↔
    c₁ * c₂ * c₃ ∣
      g * (ε₃ * c₁ * c₂ + ε₂ * c₁ * c₃ + ε₁ * c₂ * c₃) +
        ε₁ * ε₂ * ε₃ * (ε₁ * c₁ + ε₂ * c₂ + ε₃ * c₃)

/-! ## Absolute Lucas pseudoprimes -/

/-- **$D$-Carmichael number.** Let $D$ be an integer. A natural number $n$ is a $D$-Carmichael
number when $D \equiv 0$ or $1 \pmod 4$, $n > 1$ is odd and composite, $D$ and $n$ are coprime,
and for all integers $P$ and $Q \ne 0$ with $P$ and $Q$ coprime, $P^2 - 4Q = D$ and $Q$ coprime
to $n$, the number $n$ divides the term $U_{n - \varepsilon_n}(P, Q)$ of the Lucas sequence
$U(P, Q)$, where $\varepsilon_n = \left(\frac{D}{n}\right)$ is the Jacobi symbol.

These are Williams' absolute Lucas $D$-pseudoprimes. The condition on $D$ is the paper's standing
assumption; for other $D$ no Lucas sequence has discriminant $D$, so the last clause would be
vacuous.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of absolute Lucas `D`-pseudoprimes, after [17]). -/
def IsDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  (D % 4 = 0 ∨ D % 4 = 1) ∧ Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ IsCoprime D n ∧
    ∀ params : LucasSequenceParams, params.IsCoprime → params.p ^ 2 - 4 * params.q = D →
      IsCoprime params.q n → (n : ℤ) ∣ lucasU params (n - jacobiSym D n).toNat

/-- **$D$-Carmichael numbers are not prime.** For every integer $D$ and every natural number $n$,
if $n$ is a $D$-Carmichael number, then $n$ is not prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1. -/
theorem IsDCarmichael.not_prime {D : ℤ} {n : ℕ} (h : IsDCarmichael D n) : ¬ n.Prime :=
  h.2.2.2.1

/-- **$9$ is not a $5$-Carmichael number.** The number $9$ is not a $D$-Carmichael number for
$D = 5$. Indeed, the Jacobi symbol $(5 \mid 9)$ equals $1$, and the Fibonacci sequence
$U(1, -1)$ has $F_8 = 21$, which $9$ does not divide.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1. -/
theorem not_isDCarmichael_five_nine : ¬ IsDCarmichael 5 9 := by
  rintro ⟨-, -, -, -, -, h⟩
  have hc : fibonacciLucasParams.IsCoprime := ⟨1, 0, by simp [fibonacciLucasParams]⟩
  have hj : jacobiSym 5 9 = 1 := by norm_num
  have h9 := h fibonacciLucasParams hc (by simp [fibonacciLucasParams])
    (by simpa [fibonacciLucasParams] using (isCoprime_one_left (x := (9 : ℤ))).neg_left)
  rw [hj, lucasU_fibonacciLucasParams] at h9
  norm_num [Nat.fib_add_two] at h9

/-- **Extended digit sum.** Let $D$ be an integer and let $p \ge 2$ and $n$ be natural numbers, with
base-$p$ expansion $n = \sum_i c_i p^i$, $0 \le c_i < p$. With
$\varepsilon_p = \left(\frac{D}{p}\right)$ the Jacobi symbol, the extended digit sum of $n$ is
$s_p(n) = \sum_i c_i \varepsilon_p^i$.

For $p \le 1$ the definition gives $s_p(n) = n$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
equation (6). -/
def lucasDigitSum (D : ℤ) (p n : ℕ) : ℤ :=
  ((Nat.digits p n).mapIdx fun i c => (c : ℤ) * jacobiSym D p ^ i).sum

/-- **The extended digit sum of $6601$ in base $7$ for $D = 5$.** The base-$7$ expansion is
$6601 = 5 \cdot 7 + 7^2 + 5 \cdot 7^3 + 2 \cdot 7^4$ and the Jacobi symbol is
$\left(\frac{5}{7}\right) = -1$, so the extended digit sum with $D = 5$ is
$s_7(6601) = -5 + 1 - 5 + 2 = -7$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
equation (6) and the example `m = 6601`. -/
theorem lucasDigitSum_five_seven_6601 : lucasDigitSum 5 7 6601 = -7 := by
  have hj : jacobiSym 5 7 = -1 := by norm_num
  norm_num [lucasDigitSum, hj]

/-- **Primary $D$-Carmichael number.** Let $D$ be an integer. A natural number $n$ is a primary
$D$-Carmichael number when $n$ is a $D$-Carmichael number and
$|s_p(n) - \varepsilon_n| \le p - \varepsilon_p$ for every prime $p \mid n$, where
$\varepsilon_m = \left(\frac{D}{m}\right)$ is the Jacobi symbol and $s_p(n) = \sum_i c_i
\varepsilon_p^i$ is the extended digit sum of the base-$p$ expansion $n = \sum_i c_i p^i$.

In the paper's terms, $n$ has degree at most one: the number $d_p$ with
$s_p(n) = \varepsilon_n + d_p (p - \varepsilon_p)$ satisfies $|d_p| \le 1$ for every prime
$p \mid n$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
def IsPrimaryDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  IsDCarmichael D n ∧ ∀ p ∈ n.primeFactors,
    |lucasDigitSum D p n - jacobiSym D n| ≤ p - jacobiSym D p

/-- **Secondary $D$-Carmichael number.** Let $D$ be an integer. A natural number $n$ is a
secondary $D$-Carmichael number when $n$ is a $D$-Carmichael number,
$|s_p(n) - \varepsilon_n| \le 2 (p - \varepsilon_p)$ for every prime $p \mid n$, and
$|s_p(n) - \varepsilon_n| > p - \varepsilon_p$ for some prime $p \mid n$, where
$\varepsilon_m = \left(\frac{D}{m}\right)$ is the Jacobi symbol and $s_p(n) = \sum_i c_i
\varepsilon_p^i$ is the extended digit sum of the base-$p$ expansion $n = \sum_i c_i p^i$.

In the paper's terms, $n$ has degree exactly two: the number $d_p$ with
$s_p(n) = \varepsilon_n + d_p (p - \varepsilon_p)$ satisfies $|d_p| \le 2$ for every prime
$p \mid n$ and $|d_p| > 1$ for some.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
def IsSecondaryDCarmichael (D : ℤ) (n : ℕ) : Prop :=
  IsDCarmichael D n ∧
    (∀ p ∈ n.primeFactors, |lucasDigitSum D p n - jacobiSym D n| ≤ 2 * (p - jacobiSym D p)) ∧
    ∃ p ∈ n.primeFactors, p - jacobiSym D p < |lucasDigitSum D p n - jacobiSym D n|

/-- **Primary $D$-Carmichael numbers are $D$-Carmichael.** For every integer $D$ and natural
number $n$, if $n$ is a primary $D$-Carmichael number, then $n$ is a $D$-Carmichael number.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 3. -/
theorem IsPrimaryDCarmichael.isDCarmichael {D : ℤ} {n : ℕ} (h : IsPrimaryDCarmichael D n) :
    IsDCarmichael D n :=
  h.1

/-- **Carmichael numbers of a signature.** Let $\sigma = (\varepsilon_1, \dots, \varepsilon_r)$ be a
list of integers. A natural number $n$ is $\sigma$-Carmichael when every $\varepsilon_i$ is $1$ or
$-1$, $r \ge 2$, $n$ is odd and squarefree with exactly $r$ prime factors $p_1 < \dots < p_r$, and
$n$ is $D$-Carmichael for every integer $D \equiv 0$ or $1 \pmod 4$ whose Jacobi symbols satisfy
$\left(\frac{D}{p_i}\right) = \varepsilon_i$ for all $i$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 4. -/
def IsSignatureCarmichael (σ : List ℤ) (n : ℕ) : Prop :=
  Squarefree n ∧ Odd n ∧ 2 ≤ σ.length ∧ n.primeFactorsList.length = σ.length ∧
    (∀ e ∈ σ, e = 1 ∨ e = -1) ∧
    ∀ D : ℤ, (D % 4 = 0 ∨ D % 4 = 1) →
      n.primeFactorsList.map (fun p => jacobiSym D p) = σ → IsDCarmichael D n

/-- **$4$ is not a signature Carmichael number.** For every finite sequence $\sigma$ of integers,
$4$ is not a $\sigma$-Carmichael number, because $4$ is not squarefree.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Definition 4. -/
theorem not_isSignatureCarmichael_four (σ : List ℤ) : ¬ IsSignatureCarmichael σ 4 := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- **Universal $D$-forms.** Let $D$ be an integer, $\sigma$ a list of integers, and
$f(x) = (a_1 x + b_1) \cdots (a_k x + b_k)$ a product of linear factors with integer coefficients.
Then $f$ is a universal $D$-form with respect to $\sigma$ when: every factor has $a_i \ne 0$ and
$\gcd(a_i, b_i) = 1$; for every prime $\ell$ there is an integer $x$ with $\ell \nmid f(x)$; and
for every integer $x$ at which every factor $a_i x + b_i$ is a positive prime, the product $f(x)$
is $D$-Carmichael and the Jacobi symbols $\left(\frac{D}{p}\right)$, for $p$ running through the
prime factors of $f(x)$ in increasing order and counted with multiplicity, form the list $\sigma$.

Here $x$ ranges over all integers rather than $x \ge 0$, since forms such as $p + D x$ are
used with $D < 0$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of a universal `D`-form). -/
def IsUniversalLinearDForm (D : ℤ) (σ : List ℤ) (l : List (ℤ × ℤ)) : Prop :=
  (∀ ab ∈ l, ab.1 ≠ 0 ∧ Int.gcd ab.1 ab.2 = 1) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * (x : ℤ) + ab.2).prod) ∧
    ∀ x : ℤ, (∀ ab ∈ l, 0 < ab.1 * x + ab.2 ∧ (ab.1 * x + ab.2).natAbs.Prime) →
      IsDCarmichael D (l.map fun ab => (ab.1 * x + ab.2).natAbs).prod ∧
        ((l.map fun ab => (ab.1 * x + ab.2).natAbs).prod.primeFactorsList.map
          fun p => jacobiSym D p) = σ

/-- **$x(x+1)$ is never a universal form.** For every integer $D$ and every finite sequence
$\sigma$ of integers, the product of the linear factors $x$ and $x + 1$ is not a universal
$D$-form with respect to $\sigma$: since $x(x+1)$ is even for every integer $x$, the prime $2$
divides every value of the product.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Section 1 (definition of a universal `D`-form). -/
theorem not_isUniversalLinearDForm_mul_succ (D : ℤ) (σ : List ℤ) :
    ¬ IsUniversalLinearDForm D σ [(1, 0), (1, 1)] := by
  rintro ⟨-, h, -⟩
  obtain ⟨x, hx⟩ := h 2 Nat.prime_two
  apply hx
  simpa [mul_comm] using (Int.even_mul_succ_self x).two_dvd

/-! ## Results -/

/-- **Williams' Korselt criterion for $D$-Carmichael numbers.** Let $D$ be an integer with
$D \equiv 0$ or $1 \pmod 4$, and let $n > 1$ be an odd composite natural number coprime to $D$.
Then $n$ is a $D$-Carmichael number if and only if $n$ is squarefree and
$p - \left(\frac{D}{p}\right)$ divides $n - \left(\frac{D}{n}\right)$ for every prime $p \mid n$,
where $\left(\frac{D}{m}\right)$ is the Jacobi symbol.

Primes and $1$ satisfy the condition on the right but are not $D$-Carmichael, which is why $n$ is
assumed composite; it is assumed coprime to $D$ as in the definition.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 1 (`integers-2026-A102-thm-1`). -/
public theorem_wanted isDCarmichael_iff_korselt {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {n : ℕ}
    (hodd : Odd n) (hn : 1 < n) (hnp : ¬ n.Prime) (hDn : IsCoprime D n) :
    IsDCarmichael D n ↔
      Squarefree n ∧ ∀ p ∈ n.primeFactors, ((p : ℤ) - jacobiSym D p) ∣ ((n : ℤ) - jacobiSym D n)

/-- **Prime $k$-tuples give infinitely many primary Carmichael numbers (Wagstaff).** Suppose the
prime $k$-tuples conjecture holds in the following form: for every finite list of integer pairs
$(a_1, b_1), \dots, (a_k, b_k)$ with all $a_i \ge 1$ such that for every prime $\ell$ there is an
integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely many natural numbers $x$
for which every $a_i x + b_i$ is a positive prime. Then there are infinitely many composite natural
numbers $n > 1$ such that $a^{n-1} \equiv 1 \pmod n$ for every natural number $a$ coprime to $n$,
$n$ has exactly three distinct prime factors, and for every prime $p \mid n$ the sum of the
base-$p$ digits of $n$ equals $p$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 2 (`integers-2026-A102-thm-2`). -/
public theorem_wanted infinite_primary_carmichael_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ (∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      n.primeFactors.card = 3 ∧ ∀ p ∈ n.primeFactors, (Nat.digits p n).sum = p}.Infinite

/-- **Korselt criterion for $\sigma$-Carmichael numbers.** Let
$\sigma = (\varepsilon_1, \dots, \varepsilon_r)$ be a list of signs $\varepsilon_i \in \{1, -1\}$ of
length $r \ge 2$, put $\varepsilon_\sigma = \varepsilon_1 \cdots \varepsilon_r$, and let $n$ be an
odd natural number. Then $n$ is $\sigma$-Carmichael if and only if $n$ is squarefree, has exactly
$r$ prime factors $p_1 < \dots < p_r$, and satisfies
$p_i - \varepsilon_i \mid n - \varepsilon_\sigma$ for every $i$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 3 (`integers-2026-A102-thm-3`). -/
public theorem_wanted isSignatureCarmichael_iff {σ : List ℤ} (hσ : ∀ e ∈ σ, e = 1 ∨ e = -1)
    (hlen : 2 ≤ σ.length) {n : ℕ} (hodd : Odd n) :
    IsSignatureCarmichael σ n ↔
      Squarefree n ∧ n.primeFactorsList.length = σ.length ∧
        ∀ pe ∈ n.primeFactorsList.zip σ, ((pe.1 : ℤ) - pe.2) ∣ ((n : ℤ) - σ.prod)

/-- **Two-prime-factor $D$-Carmichael numbers.** Let $D$ be an integer and assume the prime
$k$-tuples conjecture (the paper's Conjecture 1) in the following form: for every finite list
of linear forms $a_i x + b_i$ with integers $a_i \ge 1$ and $b_i$ such that for every prime
$\ell$ there is an integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely
many natural numbers $x$ at which every $a_i x + b_i$ is a positive prime.
Then, first, for all primes $p < q$ such that $pq$ is a $D$-Carmichael number: the product of
the linear factors $Dx + p$ and $Dx + q$ is a universal $D$-form with respect to the signature
$(-1, 1)$; $q = p + 2$; for every integer $x$ at which $p + Dx$ and $q + Dx$ are both positive
primes, their product is a primary $D$-Carmichael number; and there are infinitely many
primary $D$-Carmichael numbers $n$ whose Jacobi symbols $(D \mid \cdot)$ at the prime factors
of $n$, listed in increasing order with multiplicity, are $-1, 1$. Second, a natural number
$n$ is a $5$-Carmichael number with exactly two prime factors counted with multiplicity if and
only if $n = (10x + 7)(10x + 9)$ for some natural number $x \ge 1$ with $10x + 7$ and
$10x + 9$ both prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 4 (`integers-2026-A102-thm-4`). -/
public theorem_wanted twoFactor_isDCarmichael {D : ℤ}
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ p q : ℕ, p.Prime → q.Prime → p < q → IsDCarmichael D (p * q) →
      IsUniversalLinearDForm D [-1, 1] [(D, p), (D, q)] ∧ q = p + 2 ∧
        (∀ x : ℤ, 0 < (p : ℤ) + D * x → ((p : ℤ) + D * x).natAbs.Prime →
          0 < (q : ℤ) + D * x → ((q : ℤ) + D * x).natAbs.Prime →
          IsPrimaryDCarmichael D (((p : ℤ) + D * x) * ((q : ℤ) + D * x)).natAbs) ∧
        {n : ℕ | IsPrimaryDCarmichael D n ∧
          n.primeFactorsList.map (fun r => jacobiSym D r) = [-1, 1]}.Infinite) ∧
    ∀ n : ℕ, (IsDCarmichael 5 n ∧ n.primeFactorsList.length = 2) ↔
      ∃ x : ℕ, 1 ≤ x ∧ (10 * x + 7).Prime ∧ (10 * x + 9).Prime ∧ n = (10 * x + 7) * (10 * x + 9)

/-- **Chernick-type universal forms for three prime factors.** Let $D$ be an integer and let
$3 < p_1 < p_2 < p_3$ be primes such that $p_1 p_2 p_3$ is $D$-Carmichael, and write
$\varepsilon_i = \left(\frac{D}{p_i}\right)$ for the Jacobi symbols. Let $g$ be the greatest common
divisor of $p_1 - \varepsilon_1$, $p_2 - \varepsilon_2$ and $p_3 - \varepsilon_3$, and let
$c_1, c_2, c_3$ be pairwise coprime integers with $g c_i = p_i - \varepsilon_i$ for each $i$. Then
$$(D c_1^2 c_2 c_3 x + p_1)(D c_1 c_2^2 c_3 x + p_2)(D c_1 c_2 c_3^2 x + p_3)$$
is a universal $D$-form with respect to the signature
$(\varepsilon_1, \varepsilon_2, \varepsilon_3)$.

Being $D$-Carmichael includes the condition $D \equiv 0$ or $1 \pmod 4$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 5 (`integers-2026-A102-thm-5`). -/
public theorem_wanted isUniversalLinearDForm_chernick {D : ℤ} {p₁ p₂ p₃ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime) (h3 : 3 < p₁)
    (h12 : p₁ < p₂) (h23 : p₂ < p₃) (hC : IsDCarmichael D (p₁ * p₂ * p₃))
    {g c₁ c₂ c₃ : ℤ}
    (hg : g = Int.gcd (Int.gcd (p₁ - jacobiSym D p₁) (p₂ - jacobiSym D p₂))
      (p₃ - jacobiSym D p₃))
    (hc₁ : g * c₁ = p₁ - jacobiSym D p₁) (hc₂ : g * c₂ = p₂ - jacobiSym D p₂)
    (hc₃ : g * c₃ = p₃ - jacobiSym D p₃)
    (hc₁₂ : IsCoprime c₁ c₂) (hc₁₃ : IsCoprime c₁ c₃) (hc₂₃ : IsCoprime c₂ c₃) :
    IsUniversalLinearDForm D [jacobiSym D p₁, jacobiSym D p₂, jacobiSym D p₃]
      [(D * c₁ ^ 2 * c₂ * c₃, p₁), (D * c₁ * c₂ ^ 2 * c₃, p₂), (D * c₁ * c₂ * c₃ ^ 2, p₃)]

/-- **Prime $k$-tuples give primary $5$-Carmichael numbers of every three-term signature.**
Suppose the prime $k$-tuples conjecture holds in the following form: for every finite list of
integer pairs $(a_1, b_1), \dots, (a_k, b_k)$ with all $a_i \ge 1$ such that for every prime
$\ell$ there is an integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely many
natural numbers $x$ for which every $a_i x + b_i$ is a positive prime. Then for all signs
$\sigma_1, \sigma_2, \sigma_3 \in \{1, -1\}$ there are infinitely many primary $5$-Carmichael
numbers $n$ that have exactly three prime factors $p_1 \le p_2 \le p_3$ counted with multiplicity
and satisfy $\left(\frac{5}{p_i}\right) = \sigma_i$ for $i = 1, 2, 3$, where
$\left(\frac{5}{p}\right)$ is the Jacobi symbol.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 6 (`integers-2026-A102-thm-6`). -/
public theorem_wanted infinite_primary_fiveCarmichael_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite)
    (σ : List ℤ) (hσ : ∀ e ∈ σ, e = 1 ∨ e = -1) (hlen : σ.length = 3) :
    {n : ℕ | IsPrimaryDCarmichael 5 n ∧
      n.primeFactorsList.map (fun p => jacobiSym 5 p) = σ}.Infinite

/-- **The $D$-Carmichael numbers of the form $3qr$.** Let $q < r$ be primes with $3 < q$. Then
$3qr$ is a $D$-Carmichael number for some integer $D$ if and only if $3qr$ is one of $105$,
$195$, $255$, $399$, $561$ and $2703$. Moreover, for all integers $D$ and $D'$ such that $3qr$
is both $D$-Carmichael and $D'$-Carmichael, the Jacobi symbols agree at $3$, $q$ and $r$:
$(D \mid 3) = (D' \mid 3)$, $(D \mid q) = (D' \mid q)$ and $(D \mid r) = (D' \mid r)$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 7 (`integers-2026-A102-thm-7`). -/
public theorem_wanted threeQR_isDCarmichael_iff {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (h3q : 3 < q) (hqr : q < r) :
    ((∃ D : ℤ, IsDCarmichael D (3 * q * r)) ↔
      3 * q * r ∈ ({105, 195, 255, 399, 561, 2703} : Finset ℕ)) ∧
    ∀ D D' : ℤ, IsDCarmichael D (3 * q * r) → IsDCarmichael D' (3 * q * r) →
      jacobiSym D 3 = jacobiSym D' 3 ∧ jacobiSym D q = jacobiSym D' q ∧
        jacobiSym D r = jacobiSym D' r

/-- **Primary and secondary $5$-Carmichael numbers from prime quadruples.** Assume the prime
$k$-tuples conjecture (the paper's Conjecture 1) in the following form: for every finite list
of linear forms $a_i x + b_i$ with integers $a_i \ge 1$ and $b_i$ such that for every prime
$\ell$ there is an integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely
many natural numbers $x$ at which every $a_i x + b_i$ is a positive prime.
For a natural number $x$ put $p = 30x + 17$, $q = 30x + 19$, $r = 180x + 107$ and
$s = 180x + 109$. Then, first, for every natural number $x$ with $p$, $q$, $r$ and $s$ all
prime, $pqr$ and $pqs$ are primary $5$-Carmichael numbers and $pqrs$ is a secondary
$5$-Carmichael number; and second, there are infinitely many natural numbers $x$ with $p$,
$q$, $r$ and $s$ all prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 8 (`integers-2026-A102-thm-8`). -/
public theorem_wanted primaryFiveCarmichael_pairs_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ x : ℕ, (30 * x + 17).Prime → (30 * x + 19).Prime → (180 * x + 107).Prime →
      (180 * x + 109).Prime →
      IsPrimaryDCarmichael 5 ((30 * x + 17) * (30 * x + 19) * (180 * x + 107)) ∧
      IsPrimaryDCarmichael 5 ((30 * x + 17) * (30 * x + 19) * (180 * x + 109)) ∧
      IsSecondaryDCarmichael 5
        ((30 * x + 17) * (30 * x + 19) * (180 * x + 107) * (180 * x + 109))) ∧
    {x : ℕ | (30 * x + 17).Prime ∧ (30 * x + 19).Prime ∧ (180 * x + 107).Prime ∧
      (180 * x + 109).Prime}.Infinite

/-- **Primary and secondary $13$-Carmichael numbers from prime quadruples.** Assume the prime
$k$-tuples conjecture (the paper's Conjecture 1) in the following form: for every finite list
of linear forms $a_i x + b_i$ with integers $a_i \ge 1$ and $b_i$ such that for every prime
$\ell$ there is an integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely
many natural numbers $x$ at which every $a_i x + b_i$ is a positive prime.
For a natural number $x$ put $p = 78x + 137$, $q = 78x + 139$, $r = 468x + 827$ and
$s = 468x + 829$. Then, first, for every natural number $x$ with $p$, $q$, $r$ and $s$ all
prime: $pqr$ and $pqs$ are primary $13$-Carmichael numbers; the Jacobi symbols
$(13 \mid \cdot)$ at the prime factors of $pqr$, listed in increasing order, are $-1, 1, -1$,
and those at the prime factors of $pqs$ are $-1, 1, 1$; and $pqrs$ is a secondary
$13$-Carmichael number. Second, there are infinitely many natural numbers $x$ with $p$, $q$,
$r$ and $s$ all prime.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 9 (`integers-2026-A102-thm-9`). -/
public theorem_wanted primaryThirteenCarmichael_pairs_of_primeKTuples
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ x : ℕ, (78 * x + 137).Prime → (78 * x + 139).Prime → (468 * x + 827).Prime →
      (468 * x + 829).Prime →
      IsPrimaryDCarmichael 13 ((78 * x + 137) * (78 * x + 139) * (468 * x + 827)) ∧
      IsPrimaryDCarmichael 13 ((78 * x + 137) * (78 * x + 139) * (468 * x + 829)) ∧
      (((78 * x + 137) * (78 * x + 139) * (468 * x + 827)).primeFactorsList.map
        fun p => jacobiSym 13 p) = [-1, 1, -1] ∧
      (((78 * x + 137) * (78 * x + 139) * (468 * x + 829)).primeFactorsList.map
        fun p => jacobiSym 13 p) = [-1, 1, 1] ∧
      IsSecondaryDCarmichael 13
        ((78 * x + 137) * (78 * x + 139) * (468 * x + 827) * (468 * x + 829))) ∧
    {x : ℕ | (78 * x + 137).Prime ∧ (78 * x + 139).Prime ∧ (468 * x + 827).Prime ∧
      (468 * x + 829).Prime}.Infinite

/-- **Universal $5$- and $13$-forms from prime quadruples.** Assume the prime
$k$-tuples conjecture (the paper's Conjecture 1) in the following form: for every finite list
of linear forms $a_i x + b_i$ with integers $a_i \ge 1$ and $b_i$ such that for every prime
$\ell$ there is an integer $x$ with $\ell \nmid \prod_i (a_i x + b_i)$, there are infinitely
many natural numbers $x$ at which every $a_i x + b_i$ is a positive prime.
Then, first, for $D = 5$ and for $D = 13$: the products of linear factors
$(390z + 137)(390z + 139)(2340z + 827)$ and $(390z + 137)(390z + 139)(2340z + 829)$ are
universal $D$-forms with respect to the signatures $(-1, 1, -1)$ and $(-1, 1, 1)$
respectively; the product $(390z + 137)(390z + 139)(2340z + 827)(2340z + 829)$ is a
universal $D$-form with respect to the signature $(-1, 1, -1, 1)$; and for every natural
number $z$ with $390z + 137$ and $390z + 139$ prime, the first product is a primary
$D$-Carmichael number if $2340z + 827$ is prime, the second is a primary $D$-Carmichael
number if $2340z + 829$ is prime, and the four-factor product is a secondary $D$-Carmichael
number if both are prime. Second, there are infinitely many natural numbers $z$ at which all
four factors are prime.

The paper (and the record) print "universal 7- and 13-forms"; $7 \not\equiv 0, 1 \pmod 4$ is
not a discriminant, and the next sentence and the proof (combining the $5$-form of Theorem 8
with the $13$-form of Theorem 9) fix it as $5$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 10 (`integers-2026-A102-thm-10`). -/
public theorem_wanted universal_fiveThirteen_forms
    (hk : ∀ l : List (ℤ × ℤ), (∀ ab ∈ l, 1 ≤ ab.1) →
      (∀ ℓ : ℕ, ℓ.Prime → ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ (l.map fun ab => ab.1 * x + ab.2).prod) →
      {x : ℕ | ∀ ab ∈ l,
        0 < ab.1 * (x : ℤ) + ab.2 ∧ (ab.1 * (x : ℤ) + ab.2).natAbs.Prime}.Infinite) :
    (∀ D ∈ ({5, 13} : Finset ℤ),
      IsUniversalLinearDForm D [-1, 1, -1] [(390, 137), (390, 139), (2340, 827)] ∧
      IsUniversalLinearDForm D [-1, 1, 1] [(390, 137), (390, 139), (2340, 829)] ∧
      IsUniversalLinearDForm D [-1, 1, -1, 1]
        [(390, 137), (390, 139), (2340, 827), (2340, 829)] ∧
      ∀ z : ℕ, (390 * z + 137).Prime → (390 * z + 139).Prime →
        ((2340 * z + 827).Prime →
          IsPrimaryDCarmichael D ((390 * z + 137) * (390 * z + 139) * (2340 * z + 827))) ∧
        ((2340 * z + 829).Prime →
          IsPrimaryDCarmichael D ((390 * z + 137) * (390 * z + 139) * (2340 * z + 829))) ∧
        ((2340 * z + 827).Prime → (2340 * z + 829).Prime →
          IsSecondaryDCarmichael D
            ((390 * z + 137) * (390 * z + 139) * (2340 * z + 827) * (2340 * z + 829)))) ∧
    {z : ℕ | (390 * z + 137).Prime ∧ (390 * z + 139).Prime ∧ (2340 * z + 827).Prime ∧
      (2340 * z + 829).Prime}.Infinite

/-- **Schinzel's Hypothesis H gives numbers that are primary $5$- and $(-11)$-Carmichael.**
Suppose Schinzel's Hypothesis H holds in the following form: for every finite set $F$ of integer
polynomials, each satisfying the Bunyakovsky condition, such that $F$ satisfies the Schinzel
condition, there are infinitely many natural numbers $n$ for which $|f(n)|$ is prime for every
$f \in F$. Then there are infinitely many natural numbers $n$ that are both primary
$5$-Carmichael and primary $(-11)$-Carmichael and have exactly three prime factors
$p_1 \le p_2 \le p_3$ counted with multiplicity, with Jacobi symbols
$\left(\frac{5}{p_1}\right) = 1$, $\left(\frac{5}{p_2}\right) = \left(\frac{5}{p_3}\right) = -1$,
$\left(\frac{-11}{p_1}\right) = \left(\frac{-11}{p_3}\right) = -1$ and
$\left(\frac{-11}{p_2}\right) = 1$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 11 (`integers-2026-A102-thm-11`). -/
public theorem_wanted infinite_primary_five_negEleven_of_schinzelH
    (hH : ∀ fs : Finset (Polynomial ℤ), (∀ f ∈ fs, Polynomial.BunyakovskyCondition f) →
      Polynomial.SchinzelCondition fs →
      {n : ℕ | ∀ f ∈ fs, (f.eval (n : ℤ)).natAbs.Prime}.Infinite) :
    {n : ℕ | IsPrimaryDCarmichael 5 n ∧
      n.primeFactorsList.map (fun p => jacobiSym 5 p) = [1, -1, -1] ∧
      IsPrimaryDCarmichael (-11) n ∧
      n.primeFactorsList.map (fun p => jacobiSym (-11) p) = [-1, 1, -1]}.Infinite

/-- **Bi-Carmichael numbers for signatures of opposite signs.** Let $D$ and $D'$ be integers and
let $n$ be both a $D$-Carmichael and a $D'$-Carmichael number whose Jacobi symbols satisfy
$\left(\frac{D}{n}\right) \ne \left(\frac{D'}{n}\right)$. Then
$\left(\frac{D'}{p}\right) = -\left(\frac{D}{p}\right)$ for every prime $p \mid n$, the number of
distinct prime factors of $n$ is odd, and $3 \nmid n$.

This reads the paper's $n \in C(\sigma) \cap C(\sigma')$ as $n$ being $D$-Carmichael with
signature $\sigma$ and $D'$-Carmichael with signature $\sigma'$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 12 (`integers-2026-A102-thm-12`). -/
public theorem_wanted isDCarmichael_opposite_signs {D D' : ℤ} {n : ℕ} (h : IsDCarmichael D n)
    (h' : IsDCarmichael D' n)
    (hs : jacobiSym D n ≠ jacobiSym D' n) :
    (∀ p ∈ n.primeFactors, jacobiSym D' p = -jacobiSym D p) ∧ Odd n.primeFactors.card ∧
      ¬ 3 ∣ n

/-- **Three-prime-factor $D$-Carmichael numbers have a single Jacobi sign.** Let $D$ and $D'$ be
integers and let $n$ be a natural number with exactly three distinct prime factors. If $n$ is both
$D$-Carmichael and $D'$-Carmichael, then the Jacobi symbols agree:
$\left(\frac{D}{n}\right) = \left(\frac{D'}{n}\right)$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Theorem 13 (`integers-2026-A102-thm-13`). -/
public theorem_wanted jacobiSym_eq_of_isDCarmichael_three {D D' : ℤ} {n : ℕ}
    (h3 : n.primeFactors.card = 3) (h : IsDCarmichael D n) (h' : IsDCarmichael D' n) :
    jacobiSym D n = jacobiSym D' n

/-- **Ballot's Lemma 3: the three divisibilities persist modulo $c_1 c_2 c_3$.** Let
$\varepsilon_1, \varepsilon_2, \varepsilon_3 \in \{1, -1\}$, let $c_1, c_2, c_3$ be pairwise coprime
positive integers, let $\varepsilon = \varepsilon_1 \varepsilon_2 \varepsilon_3$, and let $g \ne 0$
be an integer such that $c_i g$ divides
$(c_1 g + \varepsilon_1)(c_2 g + \varepsilon_2)(c_3 g + \varepsilon_3) - \varepsilon$ for
$i = 1, 2, 3$. Then every nonzero integer $h \equiv g \pmod{c_1 c_2 c_3}$ satisfies the same
divisibilities: $c_i h$ divides
$(c_1 h + \varepsilon_1)(c_2 h + \varepsilon_2)(c_3 h + \varepsilon_3) - \varepsilon$ for
$i = 1, 2, 3$.

The divisibility hypothesis on $g$ is needed: for $(c_1, c_2, c_3) = (1, 2, 3)$,
$\varepsilon_1 = \varepsilon_2 = \varepsilon_3 = 1$ and $g = h = 1$, the product is $24$ and
$2 \nmid 24 - 1$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 3 (`integers-2026-A102-lem-3`). -/
public theorem_wanted mul_dvd_prod_sub_sign_of_modEq {ε₁ ε₂ ε₃ c₁ c₂ c₃ g h : ℤ}
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1) (hε₂ : ε₂ = 1 ∨ ε₂ = -1) (hε₃ : ε₃ = 1 ∨ ε₃ = -1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (h₁₂ : IsCoprime c₁ c₂) (h₁₃ : IsCoprime c₁ c₃) (h₂₃ : IsCoprime c₂ c₃) (hg : g ≠ 0)
    (hgdvd : ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * g ∣ (c₁ * g + ε₁) * (c₂ * g + ε₂) * (c₃ * g + ε₃) - ε₁ * ε₂ * ε₃)
    (hh : h ≠ 0) (hhg : h ≡ g [ZMOD c₁ * c₂ * c₃]) :
    ∀ c ∈ ({c₁, c₂, c₃} : Finset ℤ),
      c * h ∣ (c₁ * h + ε₁) * (c₂ * h + ε₂) * (c₃ * h + ε₃) - ε₁ * ε₂ * ε₃

/-- **Divisibility conditions for $D$-Carmichael numbers $3qr$.** Let $D$ be an integer, let
$q < r$ be primes with $3 < q$, and write $\alpha = (D \mid 3)$, $\beta = (D \mid q)$ and
$\gamma = (D \mid r)$ for the Jacobi symbols. If $3qr$ is a $D$-Carmichael number, then
$q - \beta$ divides $3r - \alpha\gamma$ and $r - \gamma$ divides $3q - \alpha\beta$; moreover
$r = 3q + 2\gamma$ if $\gamma = -\alpha\beta$, and $2r = 3q + \gamma$ if $\gamma = \alpha\beta$.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Lemma 4 (`integers-2026-A102-lem-4`). -/
public theorem_wanted threeQR_isDCarmichael_divisibility {D : ℤ} {q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (h3q : 3 < q) (hqr : q < r)
    (h : IsDCarmichael D (3 * q * r)) :
    ((q : ℤ) - jacobiSym D q) ∣ (3 * r - jacobiSym D 3 * jacobiSym D r) ∧
    ((r : ℤ) - jacobiSym D r) ∣ (3 * q - jacobiSym D 3 * jacobiSym D q) ∧
    (jacobiSym D r = -(jacobiSym D 3 * jacobiSym D q) → (r : ℤ) = 3 * q + 2 * jacobiSym D r) ∧
    (jacobiSym D r = jacobiSym D 3 * jacobiSym D q → 2 * (r : ℤ) = 3 * q + jacobiSym D r)

/-- **Williams' characterization of two-prime $D$-Carmichael numbers.** Let $D$ be an integer
with $D \equiv 0$ or $1 \pmod 4$ and let $p_1 < p_2$ be primes. Then $p_1 p_2$ is a
$D$-Carmichael number if and only if $p_2 = p_1 + 2$, $\left(\frac{D}{p_1}\right) = -1$ and
$\left(\frac{D}{p_2}\right) = 1$, where $\left(\frac{D}{p}\right)$ is the Jacobi symbol.

Source: Christian Ballot, *On Absolute Lucas Pseudoprimes*, INTEGERS 26 (2026), Article A102,
Proposition 1 (`integers-2026-A102-prop-1`). -/
public theorem_wanted isDCarmichael_mul_iff {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) {p₁ p₂ : ℕ}
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h12 : p₁ < p₂) :
    IsDCarmichael D (p₁ * p₂) ↔ p₂ = p₁ + 2 ∧ jacobiSym D p₁ = -1 ∧ jacobiSym D p₂ = 1

end

end MetaMathlibExt
