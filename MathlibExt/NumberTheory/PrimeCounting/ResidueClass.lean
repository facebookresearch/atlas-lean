/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.ModEq

/-!
# Prime counting in a residue class

This file defines the inclusive finite count of primes in one residue class.
-/

@[expose] public section

namespace Nat

/-- **Prime counting in a residue class.** For natural numbers $X$, $q$ and $a$, $\pi(X; q, a)$ is
the number of primes $p \le X$ with $p \equiv a \pmod q$. The modulus $q = 1$ is allowed, and for
$q = 0$ the congruence means $p = a$. -/
def primeCountingMod (X q a : ℕ) : ℕ :=
  ((X.primesLE.filter fun p => p ≡ a [MOD q]).card)

/-- **Prime counting modulo one.** For all natural numbers $X$ and $a$, the number $\pi(X; 1, a)$
of primes $p \le X$ with $p \equiv a \pmod 1$ equals $\pi(X)$, the number of primes $p \le X$.

Modulus one imposes no residue condition. -/
theorem primeCountingMod_one (X a : ℕ) :
    primeCountingMod X 1 a = Nat.primeCounting X := by
  unfold primeCountingMod
  have hfilter : (X.primesLE.filter fun p => p ≡ a [MOD 1]) = X.primesLE := by
    apply Finset.filter_true_of_mem
    intro p _
    simp [Nat.ModEq, Nat.mod_one]
  rw [hfilter, Nat.primesLE_card_eq_primeCounting]

/-- **Residue-class prime count as a filtered range.** For all natural numbers $n$, $q$ and $a$,
the number $\pi(n; q, a)$ of primes $p \le n$ with $p \equiv a \pmod q$ equals the number of
integers $p$ with $0 \le p \le n$ such that $p$ is prime and $p \equiv a \pmod q$. -/
theorem primeCountingMod_eq_card_filter_range (n q a : ℕ) :
    Nat.primeCountingMod n q a
      = ((Finset.range (n + 1)).filter
        fun p => Nat.Prime p ∧ Nat.ModEq q p a).card := by
  unfold Nat.primeCountingMod
  rw [Nat.primesLE_eq_filter_range, Finset.filter_filter]

end Nat
