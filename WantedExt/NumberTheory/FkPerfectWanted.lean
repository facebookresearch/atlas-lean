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
are `k = 2`, `ℓ = 3`. The imported `MathlibExt` modules
define these as `IsKLDeficientPerfect`/`IsKLNearPerfect` and
the `With` variants fixing the divisor `d` (written
additively to stay in `ℕ`). The paper's `ℓ` is a positive natural (its
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
public import MathlibExt.NumberTheory.FkPerfectNotIsNearFPerfectTwoMulPrimePow
public import MathlibExt.NumberTheory.FkPerfectKlNearPerfectWithPrimePowTwoIff
public import MathlibExt.NumberTheory.FkPerfectNotIsDeficientFPerfectOfPrime
public import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul
public import MathlibExt.NumberTheory.FkPerfectNotIsNearFPerfectTwoPowMulPrime
public import MathlibExt.NumberTheory.FkPerfectNotKlDeficientPerfectWithTwoPowMul
public import MathlibExt.NumberTheory.FkPerfectIsDeficientFPerfectTwoPowMulPrimeImp
public import MathlibExt.NumberTheory.FkPerfectSquarefreeOdd

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

/-- **No deficient $F_k$-perfect number of the form $2p^a$ for $k > 2$.** Let $k > 2$, let $p$ be
an odd prime and let $a$ be a natural number. Then $2p^a$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 18. -/
theorem_wanted not_isDeficientFkPerfect_two_mul_pow
    (k p a : ℕ) (hk : 2 < k) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsDeficientFkPerfect k (2 * p ^ a)

end MathlibExt.NumberTheory.FkPerfectWanted
