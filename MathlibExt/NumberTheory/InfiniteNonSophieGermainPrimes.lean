/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.SophieGermainPrime
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Infinitely many primes are not Sophie Germain primes

Every prime `q` congruent to one modulo three has `3` as a proper divisor of `2 * q + 1`.
These primes form an infinite subset of the primes that are not Sophie Germain primes.
-/

public section

namespace MetaMathlibExt

/-- **Infinitely many primes are not Sophie Germain primes.** The set of primes $q$ that are not
Sophie Germain primes, that is, the primes $q$ for which $2q + 1$ is not prime, is infinite.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 3.1 (`integers-2025-A83-thm-3-1`). -/
theorem infinite_setOf_prime_not_isSophieGermainPrime :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime}.Infinite := by
  apply (Nat.infinite_setOfPred_prime_modEq_one (k := 3) (by decide)).mono
  rintro q ⟨hq, hmod⟩
  change q % 3 = 1 at hmod
  have hdvd : 3 ∣ 2 * q + 1 := by omega
  have hlt : 3 < 2 * q + 1 := by
    have := hq.two_le
    omega
  exact ⟨hq, fun h => Nat.not_prime_of_dvd_of_lt hdvd (by decide) hlt h.prime_two_mul_add_one⟩

end MetaMathlibExt
