/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.NumberTheory.Wilson
@[expose] public section

/-!
# Wilson quotient

This module defines the integer-valued Wilson quotient `W(p) = ((p-1)! + 1) / p`.

Primary source: Y. Matsuno, *A resolution of Kellner's conjectures on Wilson quotients*,
arXiv:2607.10106v1, lines 44–51, defines `W_p = ((p-1)! + 1) / p` for an odd prime `p`.
Downstream identity: M. Avitabile and S. Mattarei, *On some coefficients of the Artin-Hasse
series modulo a prime*, arXiv:2308.16034v1, `AH.tex` lines 315–321, uses
`(p-1)! = -1 + p * w_p`, i.e. `p * w_p = (p-1)! + 1`.

The definition is total as `ℕ → ℤ` via integer division; the source's odd-prime
domain is recorded as a hypothesis on the characterizing lemmas. Integrality
`p ∣ (p-1)! + 1` is Wilson's theorem, so the divisibility and exact-recovery
identities need only `p.Prime` (Wilson holds for `p = 2` as well); the oddness
restriction from the source is therefore not imposed on the theorems.
-/

namespace Int

/-- **Wilson quotient.** For a natural number $p$, the Wilson quotient is the integer
$W(p) = \lfloor ((p-1)! + 1) / p \rfloor$ for $p \ge 1$, and $W(0) = 0$.

For a prime $p$, Wilson's theorem $p \mid (p-1)! + 1$ makes the division exact. The definition is
total on $\mathbb{N}$; the source defines $W_p$ only for odd primes $p$.

Source: Y. Matsuno, *A resolution of Kellner's conjectures on Wilson quotients*,
arXiv:2607.10106v1, lines 44–51. -/
def wilsonQuotient (p : ℕ) : ℤ :=
  ((Nat.factorial (p - 1) : ℤ) + 1) / (p : ℤ)

/-- **Exactness of the Wilson quotient.** For every prime $p$, the Wilson quotient $W(p)$ of $p$
satisfies $p \, W(p) = (p-1)! + 1$ in $\mathbb{Z}$.

By Wilson's theorem $p$ divides $(p-1)! + 1$, so the division defining $W(p)$ is exact.

Source: M. Avitabile and S. Mattarei, arXiv:2308.16034, `AH.tex` lines 315–321, which uses
$(p-1)! = -1 + p \, w_p$, where $w_p$ is the Wilson quotient. -/
theorem mul_wilsonQuotient (p : ℕ) (hp : Nat.Prime p) :
    (p : ℤ) * wilsonQuotient p = (Nat.factorial (p - 1) : ℤ) + 1 := by
  unfold wilsonQuotient
  have h_dvd : (p : ℤ) ∣ ((Nat.factorial (p - 1) : ℤ) + 1) := by
    let _ := Fact.mk hp
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [ZMod.wilsons_lemma p]
    simp
  exact Int.mul_ediv_cancel' h_dvd

/-- **Factorial form of the Wilson quotient identity.** For every prime $p$, the Wilson
quotient $W(p)$ of $p$ satisfies $(p-1)! = p \, W(p) - 1$ in $\mathbb{Z}$.

Source: M. Avitabile and S. Mattarei, arXiv:2308.16034, `AH.tex` lines 315–321, display
$(p-1)! = -1 + p \, w_p$, where $w_p$ is the Wilson quotient. -/
theorem factorial_eq_mul_wilsonQuotient_sub_one (p : ℕ) (hp : Nat.Prime p) :
    (Nat.factorial (p - 1) : ℤ) = (p : ℤ) * wilsonQuotient p - 1 := by
  have h := mul_wilsonQuotient p hp
  omega

end Int
