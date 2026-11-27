/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On near `F_k`-perfect and deficient `F_k`-perfect numbers

Statements from Flora Jeba S, Anirban Roy, Pankaj Jyoti
Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect and
Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>).

With `σₖ(n) = ∑_{d ∣ n} d^k`, the paper calls `n`
`[k,ℓ]`-deficient-perfect if `σₖ(n) - n^k + d^k = ℓn` for
some proper divisor `d` of `n`, and `[k,ℓ]`-near-perfect if
`σₖ(n) - n^k - d^k = ℓn`; deficient/near `F_k`-perfect is
the case `ℓ = 3` (with `k > 1`), and `F`-perfect variants
are `k = 2`, `ℓ = 3`. Below these are
`IsKLDeficientPerfect`/`IsKLNearPerfect` and the `With`
variants fixing the divisor `d` (written additively to stay
in `ℕ`). The paper's `ℓ` is a positive natural (its
Proposition 2 proof needs `ℓ ≥ 1`: at `ℓ = 0` every prime
would be `[k,0]`-near-perfect with `d = 1`), so
`[k,ℓ]`-statements carry `1 ≤ l` where the printed form
needs it. Two printed statements need corrections found by brute
force: Theorem 3 omits the exception `p^a = 2` (which is
`[2,1]`-deficient-perfect, cf. Corollary 1), and Theorem
4's conclusion `a = k` is false in general (the correct
range is `2 ≤ a ≤ k`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
public import MathlibExt.NumberTheory.FkPerfect
public import MathlibExt.NumberTheory.FkPerfectIsDeficientFPerfectTwoMulPrimePow
public import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime
public import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul
public import MathlibExt.NumberTheory.FkPerfectNotIsNearFPerfectTwoPowMulPrime

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No prime power is deficient $F$-perfect or near $F$-perfect.** For every prime $p$ and
every natural number $a$, the number $n = p^a$ is neither deficient $F$-perfect nor near
$F$-perfect: there is no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) + d^2 = n^2 + 3n$, and
no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the
sum of the squares of the divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 1. -/
theorem_wanted prime_pow_not_fPerfect (p a : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect (p ^ a) ∧ ¬ IsNearFPerfect (p ^ a)

/-- **Prime powers that are $[2,\ell]$-near-perfect.** Let $p$ be a prime, let $a$, $\ell$ and
$d$ be natural numbers with $\ell \ge 1$, and write $\sigma_2(m)$ for the sum of the squares of
the divisors of $m$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and $d < p^a$) with
$\sigma_2(p^a) = (p^a)^2 + d^2 + \ell p^a$ if and only if $a = 2$, $\ell = 1$ and $d = 1$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 2. -/
theorem_wanted klNearPerfectWith_prime_pow_two_iff
    (p a l d : ℕ) (hp : p.Prime) (hl : 1 ≤ l) :
    KLNearPerfectWith 2 l (p ^ a) d ↔
      a = 2 ∧ l = 1 ∧ d = 1

/-- **Prime powers that are $[k,\ell]$-near-perfect.** Let $p$ be a prime, let $a$, $k$, $\ell$
and $d$ be natural numbers with $k \ge 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and
$d < p^a$) with $\sigma_k(p^a) = (p^a)^k + d^k + \ell p^a$ if and only if $2 \le a \le k$,
$d = 1$ and $\ell = p^{k-a} \sum_{i=0}^{a-2} p^{ik}$.

The source prints the conclusion $a = k$, which is false: for $p = 2$, $a = 2$, $k = 3$,
$\ell = 2$, $d = 1$ one has $\sigma_3(4) = 73 = 4^3 + 1^3 + 2 \cdot 4$ with $a \ne k$. The
printed form is the case $a = k$ of the identity $\sum_{i=1}^{a-1} p^{ik} = \ell p^a$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 4. -/
theorem_wanted klNearPerfectWith_prime_pow_iff
    (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    KLNearPerfectWith k l (p ^ a) d ↔
      2 ≤ a ∧ a ≤ k ∧ d = 1 ∧
        l = p ^ (k - a) *
          ∑ i ∈ Finset.range (a - 1), p ^ (i * k)

/-- **$[k,\ell]$-deficient-perfect prime powers for $k \ge 2$.** Let $p$ be a prime and let $a$,
$k$ and $\ell$ be natural numbers with $k \ge 2$. If $p^a$ is $[k,\ell]$-deficient-perfect, then
$p = 2$ and $a = 1$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem_wanted isKLDeficientPerfect_prime_pow_imp
    (p a k l : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    IsKLDeficientPerfect k l (p ^ a) → p = 2 ∧ a = 1

/-- **Twice an odd prime is not $[k,\ell]$-near-perfect.** Let $k$ and $\ell$ be natural numbers
with $\ell \ge 1$ and let $p$ be an odd prime. Then $2p$ is not $[k,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 6. -/
theorem_wanted not_isKLNearPerfect_two_mul_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect k l (2 * p)

/-- **Deficient $F$-perfect numbers of the form $2^a p$.** Let $p$ be a prime and $a$ a natural
number. If $2^a p$ is deficient $F$-perfect, then $p = 3$ and $a = 1$, so the number is $6$.

The number $6$ is indeed deficient $F$-perfect, with $d = 2$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 7. -/
theorem_wanted isDeficientFPerfect_two_pow_mul_prime_imp
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect (2 ^ a * p) → p = 3 ∧ a = 1

/-- **$2^a p$ is not $[k,\ell]$-deficient-perfect with divisor $1$ or $p$.** Let $k$, $\ell$, $a$
be natural numbers with $\ell \ge 1$ and let $p$ be an odd prime. Call $n$
$[k,\ell]$-deficient-perfect with divisor $d$ when $d$ divides $n$, $d < n$ and
$\sigma_k(n) + d^k = n^k + \ell n$, where $\sigma_k(n)$ is the sum of the $k$-th powers of the
divisors of $n$. Then $2^a p$ is not $[k,\ell]$-deficient-perfect with divisor $1$, and not with
divisor $p$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 8. -/
theorem_wanted not_klDeficientPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ KLDeficientPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLDeficientPerfectWith k l (2 ^ a * p) p

/-- **For $a \ge 2$, $2^a p$ is not $[k,\ell]$-near-perfect with divisor $1$ or $p$.** Let $k$,
$\ell$, $a$ be natural numbers with $\ell \ge 1$ and $a \ge 2$, and let $p$ be an odd prime. Call
$n$ $[k,\ell]$-near-perfect with divisor $d$ when $d$ divides $n$, $d < n$ and
$\sigma_k(n) = n^k + d^k + \ell n$, where $\sigma_k(n)$ is the sum of the $k$-th powers of the
divisors of $n$. Then $2^a p$ is not $[k,\ell]$-near-perfect with divisor $1$, and not with
divisor $p$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 11. -/
theorem_wanted not_klNearPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p)
    (ha : 1 < a) :
    ¬ KLNearPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLNearPerfectWith k l (2 ^ a * p) p

/-- **No near $F$-perfect number of the form $2p^a$.** For every prime $p$ and every natural
number $a$, the number $n = 2p^a$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 13. -/
theorem_wanted not_isNearFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 * p ^ a)

/-- **No deficient $F_k$-perfect number $p_1^a p_2$ with distinct odd primes.** Let $k > 1$ be
a natural number, let $p_1 \ne p_2$ be odd primes and let $a$ be a natural number. Then
$p_1^a p_2$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 16. -/
theorem_wanted not_isDeficientFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂)

/-- **No deficient $F_k$-perfect number of the form $2p^a$ for $k > 2$.** Let $k > 2$, let $p$ be
an odd prime and let $a$ be a natural number. Then $2p^a$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 18. -/
theorem_wanted not_isDeficientFkPerfect_two_mul_pow
    (k p a : ℕ) (hk : 2 < k) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsDeficientFkPerfect k (2 * p ^ a)

/-- **No near $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural numbers such that
$a + b$ is odd or both $a$ and $b$ are odd. Then $p_1^a p_2^b$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 20. -/
theorem_wanted not_isNearFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂ ^ b)

/-- **No product of distinct odd primes is near $F_k$-perfect.** Let $k > 1$ and let $s$ be a
finite set of odd primes. Then $\prod_{p \in s} p$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 22. -/
theorem_wanted not_isNearFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsNearFkPerfect k (∏ p ∈ s, p)

end MathlibExt.NumberTheory.FkPerfectWanted
