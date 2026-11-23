/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting

/-!
# Ramanujan prime

Formalizes the required definition clause for the Ramanujan prime concept
(concept `jis_sem_2ce4a4483a6ae69670d63026`, statement `jis_b3eb662622ec0b548e5acec4`,
source `jis_source_04b544b932aca55da03d6b0c`).

Source: Vladimir Shevelev,
*Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Primes satisfying the Ramanujan counting condition.** Let $\pi$ be the prime-counting
function. For natural numbers $R$ and $n$, $R$ satisfies the Ramanujan counting condition for
$n$ when $R$ is prime and $\pi(R) - \pi(R/2) = n$.

Here $\pi(x)$ counts the primes $p \le x$, so $\pi(R/2) = \pi(\lfloor R/2 \rfloor)$.

Source: concept `jis_sem_2ce4a4483a6ae69670d63026`; statement `jis_b3eb662622ec0b548e5acec4`.
-/
public def IsRamanujanPrime (R n : ℕ) : Prop :=
  Nat.Prime R ∧ (Nat.primeCounting R - Nat.primeCounting (R / 2) = n)

/-- **The $n$-th Ramanujan prime.** Let $\pi$ be the prime-counting function. For natural numbers
$R$ and $n$, $R$ is the $n$-th Ramanujan prime when $n \ge 1$, $R$ is a prime with
$\pi(R) - \pi(R/2) = n$, and every prime $p$ with $\pi(p) - \pi(p/2) = n$ satisfies $p \le R$.
That is, $R$ is the largest prime satisfying the Ramanujan counting condition for $n$.

Here $\pi(x)$ counts the primes $p \le x$, so $\pi(R/2) = \pi(\lfloor R/2 \rfloor)$.

Source: concept `jis_sem_2ce4a4483a6ae69670d63026`; statement `jis_b3eb662622ec0b548e5acec4`.
-/
public def IsNthRamanujanPrime (R n : ℕ) : Prop :=
  1 ≤ n ∧ IsRamanujanPrime R n ∧ ∀ p : ℕ, IsRamanujanPrime p n → p ≤ R

end

end MetaMathlibExt
