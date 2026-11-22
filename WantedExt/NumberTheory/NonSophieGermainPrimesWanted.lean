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

/-- There are infinitely many primes that are not Sophie Germain primes: the
set `T` of primes `q` for which `2q + 1` is not prime is infinite.

Here `T` is the paper's set of primes that are not Sophie Germain primes
("`a ∈ T`, i.e., `a` is not a Sophie Germain prime"), and a Sophie Germain prime
is a prime `p` with `2p + 1` prime (`Nat.IsSophieGermainPrime`).

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 3.1 (`integers-2025-A83-thm-3-1`). -/
public theorem_wanted infinite_setOf_prime_not_isSophieGermainPrime :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime}.Infinite

/-- The primes that are not Sophie Germain primes are exactly the primes in
`A = ⋃_{p odd prime} A(p)`, where `A(p) = {p r + (p - 1)/2 : r = 1, 2, 3, …}`; equivalently,
the Sophie Germain primes are the primes outside `A`.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 2.1 (`integers-2025-A83-thm-2-1`). -/
public theorem_wanted setOf_prime_not_isSophieGermainPrime_eq_inter :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime} =
      {q : ℕ | q.Prime} ∩
        {q : ℕ | ∃ p r : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ r ∧ q = p * r + (p - 1) / 2}

/-- Wilson-type characterization: for an integer `a ≥ 2`, `a` is a Sophie Germain prime other
than `2` exactly when `(a - 1)! ≡ 2a - 1` or `(a - 1)! ≡ -(6a + 1) (mod a(2a + 1))`. The paper
states this for all `a ∈ ℤ⁺`; at `a = 1` the first congruence holds (`0! = 1 ≡ 1 (mod 3)`)
while `1` is not prime (the proof's appeal to Wilson's theorem modulo `a` needs `a ≥ 2`).

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 5.3 (`integers-2025-A83-thm-5-3`). -/
public theorem_wanted isSophieGermainPrime_ne_two_iff_factorial_modEq {a : ℕ} (ha : 2 ≤ a) :
    (a.IsSophieGermainPrime ∧ a ≠ 2) ↔
      ((a - 1).factorial : ℤ) ≡ 2 * a - 1 [ZMOD a * (2 * a + 1)] ∨
        ((a - 1).factorial : ℤ) ≡ -(6 * a + 1) [ZMOD a * (2 * a + 1)]

end

end MetaMathlibExt
