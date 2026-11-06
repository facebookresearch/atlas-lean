/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Sophie Germain primes

This module defines the Sophie Germain prime predicate following arXiv:2311.13375,
lines 83–85: a prime `p` such that `2 * p + 1` is also prime. No oddness
restriction is imposed, so `p = 2` is included.

## Main definitions

* `Nat.IsSophieGermainPrime`

## Main statements

* `Nat.isSophieGermainPrime_iff`
* `Nat.IsSophieGermainPrime.prime`
* `Nat.IsSophieGermainPrime.prime_two_mul_add_one`
-/

@[expose] public section

namespace Nat

/-- **Sophie Germain primes.** A natural number $p$ is a Sophie Germain prime if $p$ is prime and
$2p + 1$ is prime. The case $p = 2$ is not excluded.

Source: arXiv:2311.13375, lines 83–85. -/
def IsSophieGermainPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- **Characterization of Sophie Germain primes.** A natural number $p$ is a Sophie Germain prime
if and only if $p$ is prime and $2p + 1$ is prime. -/
theorem isSophieGermainPrime_iff (p : ℕ) :
    IsSophieGermainPrime p ↔ Nat.Prime p ∧ Nat.Prime (2 * p + 1) :=
  Iff.rfl

/-- **Sophie Germain primes are prime.** If $p$ is a Sophie Germain prime, then $p$ is prime. -/
theorem IsSophieGermainPrime.prime {p : ℕ} (h : IsSophieGermainPrime p) :
    Nat.Prime p :=
  h.1

/-- **Safe prime of a Sophie Germain prime.** If $p$ is a Sophie Germain prime, then $2p + 1$ is
prime. -/
theorem IsSophieGermainPrime.prime_two_mul_add_one {p : ℕ} (h : IsSophieGermainPrime p) :
    Nat.Prime (2 * p + 1) :=
  h.2

end Nat
