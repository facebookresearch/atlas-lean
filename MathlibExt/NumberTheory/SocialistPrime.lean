/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Order.Interval.Set.Nat

@[expose] public section

/-!
# Socialist primes

Definition from Trudgian, *There are no socialist primes less than 10^9*,
arXiv:1310.6403v2, line 24:

> Erdős asked whether there exist any primes $p>5$ for which the numbers
> $2!, 3!, \ldots, (p-1)!$ are all distinct modulo $p$.

A socialist prime is a prime `p > 5` such that the natural residues
`k ! % p` for `k ∈ Set.Icc 2 (p-1)` are pairwise distinct.
Equality of natural remainders is equivalent to congruence mod `p` for `p>0`.
-/

namespace Nat

/-- **Socialist primes.** A natural number $p$ is a socialist prime if $p$ is prime, $p > 5$, and
the factorials $2!, 3!, \ldots, (p-1)!$ have pairwise distinct remainders modulo $p$.

Source: Trudgian, arXiv:1310.6403v2, line 24. -/
def IsSocialistPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ 5 < p ∧
    Set.Pairwise (Set.Icc 2 (p - 1)) (fun k l => k.factorial % p ≠ l.factorial % p)

theorem IsSocialistPrime.prime {p : ℕ} (h : IsSocialistPrime p) : Nat.Prime p :=
  h.1

theorem IsSocialistPrime.five_lt {p : ℕ} (h : IsSocialistPrime p) : 5 < p :=
  h.2.1

theorem IsSocialistPrime.pairwise {p : ℕ} (h : IsSocialistPrime p) :
    Set.Pairwise (Set.Icc 2 (p - 1)) (fun k l => k.factorial % p ≠ l.factorial % p) :=
  h.2.2

/-- **Distinct factorial residues modulo a socialist prime.** Let $p$ be a socialist prime. If $a$
and $b$ are distinct natural numbers with $2 \le a \le p - 1$ and $2 \le b \le p - 1$, then
$a!$ and $b!$ have different remainders modulo $p$. -/
theorem IsSocialistPrime.factorial_mod_ne {p : ℕ} (h : IsSocialistPrime p)
    {a b : ℕ} (ha : a ∈ Set.Icc 2 (p - 1)) (hb : b ∈ Set.Icc 2 (p - 1))
    (hab : a ≠ b) : a.factorial % p ≠ b.factorial % p :=
  h.pairwise ha hb hab

end Nat

end
