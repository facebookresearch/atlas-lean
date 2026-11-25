/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.PrimeCounting

/-!
# Labos primes

This file formalizes Definition 2 from Vladimir Shevelev,
*Ramanujan and Labos Primes, Their Generalizations, and Classifications of Primes*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Shevelev/shevelev19.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Labos prime.** Write $\pi(x)$ for the number of primes $p \le x$. For natural numbers $n$
and $L$, $L$ is the $n$-th Labos prime when $n \ge 1$, $L \ge 1$,
$\pi(L) - \pi(\lfloor L/2 \rfloor) = n$, and no integer $m$ with $1 \le m < L$ satisfies
$\pi(m) - \pi(\lfloor m/2 \rfloor) = n$; that is, $L$ is the least positive integer with
$\pi(L) - \pi(\lfloor L/2 \rfloor) = n$. -/
def IsLabosPrime (n L : ℕ) : Prop :=
  1 ≤ n ∧ 0 < L ∧ Nat.primeCounting L - Nat.primeCounting (L / 2) = n ∧
    ∀ m, 0 < m → m < L → Nat.primeCounting m - Nat.primeCounting (m / 2) ≠ n

end MetaMathlibExt
