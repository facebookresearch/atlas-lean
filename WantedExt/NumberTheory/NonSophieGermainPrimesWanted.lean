/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.SophieGermainPrime

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many primes are not Sophie Germain primes.** The set of primes $q$ that are not
Sophie Germain primes, that is, the primes $q$ for which $2q + 1$ is not prime, is infinite.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 3.1 (`integers-2025-A83-thm-3-1`). -/
public theorem_wanted infinite_setOf_prime_not_isSophieGermainPrime :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime}.Infinite

/-- **Primes that are not Sophie Germain primes.** For an odd prime $p$, let
$A(p) = \{pr + (p - 1)/2 : r = 1, 2, 3, \dots\}$, and let $A$ be the union of the sets $A(p)$ over
all odd primes $p$. A prime is not a Sophie Germain prime if and only if it lies in $A$;
equivalently, the Sophie Germain primes are exactly the primes outside $A$.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 2.1 (`integers-2025-A83-thm-2-1`). -/
public theorem_wanted setOf_prime_not_isSophieGermainPrime_eq_inter :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime} =
      {q : ℕ | q.Prime} ∩
        {q : ℕ | ∃ p r : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ r ∧ q = p * r + (p - 1) / 2}

/-- **Wilson-type characterization of Sophie Germain primes.** Let $a \ge 2$ be a natural number.
Then $a$ is a Sophie Germain prime other than $2$ if and only if
$(a - 1)! \equiv 2a - 1 \pmod{a(2a + 1)}$ or $(a - 1)! \equiv -(6a + 1) \pmod{a(2a + 1)}$, the
congruences being taken in the integers.

The paper states this for all positive integers $a$; at $a = 1$ the first congruence holds
($0! = 1 \equiv 1 \pmod 3$) while $1$ is not prime (the proof's appeal to Wilson's theorem modulo
$a$ needs $a \ge 2$).

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 5.3 (`integers-2025-A83-thm-5-3`). -/
public theorem_wanted isSophieGermainPrime_ne_two_iff_factorial_modEq {a : ℕ} (ha : 2 ≤ a) :
    (a.IsSophieGermainPrime ∧ a ≠ 2) ↔
      ((a - 1).factorial : ℤ) ≡ 2 * a - 1 [ZMOD a * (2 * a + 1)] ∨
        ((a - 1).factorial : ℤ) ≡ -(6 * a + 1) [ZMOD a * (2 * a + 1)]

end

end MetaMathlibExt
