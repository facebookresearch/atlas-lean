/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.NonSophieGermainPrimes
public import MathlibExt.NumberTheory.SophieGermainPrimeWilson

namespace MetaMathlibExt

@[expose] public section

/-- **Infinitely many primes are not Sophie Germain primes.** The set of primes $q$ that are not
Sophie Germain primes, that is, the primes $q$ for which $2q + 1$ is not prime, is infinite.

Source: Takashi Agoh, *A Note on Sophie Germain Primes*, INTEGERS 25 (2025),
Article A83, Theorem 3.1 (`integers-2025-A83-thm-3-1`). -/
public theorem_wanted infinite_setOf_prime_not_isSophieGermainPrime :
    {q : ℕ | q.Prime ∧ ¬ q.IsSophieGermainPrime}.Infinite

end

end MetaMathlibExt
