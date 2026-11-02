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

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-deficient-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$
and $d$, the number $n$ is $[k,\ell]$-deficient-perfect with divisor $d$ when $d$ is a proper
divisor of $n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) + d^k = n^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLDeficientPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) + d ^ k = n ^ k + l * n

/-- **$[k,\ell]$-deficient-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-deficient-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) + d^k = n^k + \ell n$. -/
def IsKLDeficientPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLDeficientPerfectWith k l n d

/-- **$[k,\ell]$-near-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$ and
$d$, the number $n$ is $[k,\ell]$-near-perfect with divisor $d$ when $d$ is a proper divisor of
$n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) = n^k + d^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLNearPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) = n ^ k + d ^ k + l * n

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$. -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

/-- **Deficient $F$-perfect numbers.** For a natural number $n$, write
$\sigma_2(n) = \sum_{e \mid n} e^2$. The number $n$ is deficient $F$-perfect when it is
$[2,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_2(n) + d^2 = n^2 + 3n$. -/
def IsDeficientFPerfect (n : ℕ) : Prop :=
  IsKLDeficientPerfect 2 3 n

/-- **Near $F$-perfect numbers.** A natural number $n$ is near $F$-perfect when it is
$[2,3]$-near-perfect, that is, when some proper divisor $d$ of $n$ ($d \mid n$ and $d < n$)
satisfies $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n) = \sum_{e \mid n} e^2$ is the sum
of the squares of the divisors of $n$. -/
def IsNearFPerfect (n : ℕ) : Prop :=
  IsKLNearPerfect 2 3 n

/-- **Odd primes are not $[k,\ell]$-deficient-perfect.** Let $p$ be an odd prime. Then for all
natural numbers $k$ and $\ell$, $p$ is not $[k,\ell]$-deficient-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 1. -/
theorem_wanted not_isKLDeficientPerfect_of_prime_odd
    (k l p : ℕ) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLDeficientPerfect k l p

/-- **$2$ is $[k,1]$-deficient-perfect.** For every natural number $k$, the number $2$ is
$[k,1]$-deficient-perfect.

The divisor is $d = 1$, since $1 + 2^k + 1^k = 2^k + 1 \cdot 2$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Corollary 1. -/
theorem_wanted isKLDeficientPerfect_two (k : ℕ) :
    IsKLDeficientPerfect k 1 2

/-- **No prime is deficient $F$-perfect.** If $p$ is a prime, then $p$ is not deficient
$F$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Corollary 2. -/
theorem_wanted not_isDeficientFPerfect_of_prime (p : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect p

/-- **Primes are not $[k,\ell]$-near-perfect.** Let $k$ and $\ell$ be natural numbers with
$\ell \ge 1$ and let $p$ be a prime. Then $p$ is not $[k,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 2. -/
theorem_wanted not_isKLNearPerfect_of_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) :
    ¬ IsKLNearPerfect k l p

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

/-- **$[2,\ell]$-deficient-perfect prime powers (corrected).** Let $p$ be a prime and let $a$ and
$\ell$ be natural numbers. If $p^a$ is $[2,\ell]$-deficient-perfect, then $\ell = 1$, and either
$a = 2$, or $p = 2$ and $a = 1$.

The printed statement allows only the exception $a = 2$, $\ell = 1$, and so omits the solution
$p = 2$, $a = 1$, $\ell = 1$, $d = 1$ (the number $2$ of Corollary 1).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3. -/
theorem_wanted isKLDeficientPerfect_prime_pow_two_imp
    (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) →
      l = 1 ∧ (a = 2 ∨ (p = 2 ∧ a = 1))

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

/-- **Prime powers that are $[1,\ell]$-deficient-perfect with a given divisor.** Let $p$ be a
prime, let $a$, $\ell$ and $d$ be natural numbers, and write $\sigma_1(m)$ for the sum of the
divisors of $m$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and $d < p^a$) with
$\sigma_1(p^a) + d = p^a + \ell p^a$ if and only if $p = 2$, $\ell = 1$, $d = 1$ and $a \ge 1$.

This is the $k = 1$ part of Theorem 5 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem_wanted klDeficientPerfectWith_one_prime_pow_iff
    (p a l d : ℕ) (hp : p.Prime) :
    KLDeficientPerfectWith 1 l (p ^ a) d ↔
      p = 2 ∧ l = 1 ∧ d = 1 ∧ 1 ≤ a

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

/-- **No near $F$-perfect number of the form $2^a p$.** For every prime $p$ and every natural
number $a$, the number $n = 2^a p$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 9. -/
theorem_wanted not_isNearFPerfect_two_pow_mul_prime
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 ^ a * p)

/-- **No $[2,\ell]$-near-perfect number of the form $2^a p$.** Let $\ell$ and $a$ be natural
numbers with $\ell \ge 1$, and let $p$ be an odd prime. Then $2^a p$ is not
$[2,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 10. -/
theorem_wanted not_isKLNearPerfect_two_two_pow_mul
    (l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect 2 l (2 ^ a * p)

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

/-- **The only deficient $F$-perfect number of the form $2p^a$ is $6$.** The number $6$ is deficient
$F$-perfect, and for every prime $p$ and every natural number $a$, if $2p^a$ is deficient
$F$-perfect then $2p^a = 6$.

The divisor for $6$ is $d = 2$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 12. -/
theorem_wanted isDeficientFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect 6 ∧
      (IsDeficientFPerfect (2 * p ^ a) → 2 * p ^ a = 6)

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

/-- **The only $[1,\ell]$-near-perfect number of the form $2p^a$ is $18$.** For natural numbers
$\ell$ and $n$, say that $n$ is $[1,\ell]$-near-perfect when some divisor $d$ of $n$ with $d < n$
satisfies $\sigma(n) = n + d + \ell n$, where $\sigma(n)$ is the sum of the divisors of $n$. Then
$18$ is $[1,1]$-near-perfect, and for every odd prime $p$ and all natural numbers $a$ and
$\ell \ge 1$, if $2p^a$ is $[1,\ell]$-near-perfect then $2p^a = 18$.

The divisor for $18$ is $d = 3$. This is part 1 of Theorem 14 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem_wanted isKLNearPerfect_one_two_mul_prime_pow
    (p a l : ℕ) (hp : p.Prime) (hpo : Odd p) (hl : 1 ≤ l) :
    IsKLNearPerfect 1 1 18 ∧
      (IsKLNearPerfect 1 l (2 * p ^ a) → 2 * p ^ a = 18)

/-- **A divisibility condition for near-perfect numbers $2p^a$.** Let $p$ be an odd prime, let
$a$, $k$, $\ell$ and $d$ be natural numbers with $k > 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. If $d$ is a proper divisor of $2p^a$ ($d \mid 2p^a$ and
$d < 2p^a$) with $\sigma_k(2p^a) = (2p^a)^k + d^k + \ell \cdot 2p^a$, then $p^2 \mid 1 + 2^k$,
and $a$ is even if and only if $d$ is odd.

This is part 2 of Theorem 14 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem_wanted klNearPerfectWith_two_mul_prime_pow_imp
    (p a k l d : ℕ) (hp : p.Prime) (hpo : Odd p) (hk : 1 < k)
    (hl : 1 ≤ l) :
    KLNearPerfectWith k l (2 * p ^ a) d →
      p ^ 2 ∣ 1 + 2 ^ k ∧ (Even a ↔ Odd d)

/-- **No near $F$-perfect number of the form $2^a p^b$ with $b$ even.** For every prime $p$ and
all natural numbers $a$ and $b$ with $b$ even, the number $n = 2^a p^b$ is not near $F$-perfect:
there is no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where
$\sigma_2(n)$ is the sum of the squares of the divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 15. -/
theorem_wanted not_isNearFPerfect_two_pow_mul_prime_pow
    (p a b : ℕ) (hp : p.Prime) (hb : Even b) :
    ¬ IsNearFPerfect (2 ^ a * p ^ b)

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

/-- **No near $F_k$-perfect number of the form $p_1^a p_2$.** Let $k > 1$, let $p_1$ and $p_2$ be
distinct odd primes and let $a$ be a natural number. Then $p_1^a p_2$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 17. -/
theorem_wanted not_isNearFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂)

/-- **No deficient $F_k$-perfect number of the form $2p^a$ for $k > 2$.** Let $k > 2$, let $p$ be
an odd prime and let $a$ be a natural number. Then $2p^a$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 18. -/
theorem_wanted not_isDeficientFkPerfect_two_mul_pow
    (k p a : ℕ) (hk : 2 < k) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsDeficientFkPerfect k (2 * p ^ a)

/-- **No deficient $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$ be a natural number, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural
numbers such that $a + b$ is odd or both $a$ and $b$ are odd. Then $n = p_1^a p_2^b$ is not
deficient $F_k$-perfect: there is no divisor $d$ of $n$ with $d < n$ and
$\sigma_k(n) + d^k = n^k + 3n$, where $\sigma_k(n) = \sum_{e \mid n} e^k$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 19. -/
theorem_wanted not_isDeficientFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂ ^ b)

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

/-- **No product of distinct odd primes is deficient $F_k$-perfect.** Let $k > 1$ and let $s$ be a
finite set of odd primes. Then $\prod_{p \in s} p$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 21. -/
theorem_wanted not_isDeficientFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsDeficientFkPerfect k (∏ p ∈ s, p)

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
