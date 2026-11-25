/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Fermat
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.NumberTheory.FermatNumberSquareFactors
public import MathlibExt.NumberTheory.GeneralizedFermatGCD
public import MathlibExt.NumberTheory.GeneralizedFermatPeriod
public import MathlibExt.NumberTheory.GeneralizedFermatShiftDivisibility
public import MathlibExt.NumberTheory.GeneralizedFermatSquareFactors
public import MathlibExt.NumberTheory.GeneralizedFermatWieferich
public import MathlibExt.NumberTheory.WieferichPrime
public import MathlibExt.NumberTheory.WieferichOrder

/-!
# Notes on Jakóbczyk's hypothesis on Fermat numbers

Statements from Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat
Numbers*, INTEGERS 26 (2026), Article A77, about the Fermat numbers
`F_n = 2^{2^n} + 1` (Mathlib's `Nat.fermatNumber`), their generalizations
`F_n(a, b) = a^{b^n} + 1`, and Wieferich primes to base `2` (`Nat.IsWieferichPrime`, i.e.
`p² ∣ 2^{p-1} - 1`) and to base `a` (`a^{p-1} ≡ 1 (mod p²)`).

The characterization of Wieferich primes to base `a` by multiplicative orders,
`MetaMathlibExt.pow_sub_one_modEq_one_sq_iff_orderOf_eq`, is proved in
`MathlibExt.NumberTheory.WieferichOrder`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Warren–Bray congruence for prime divisors of Fermat numbers.** Let $F_n = 2^{2^n} + 1$ be
the $n$-th Fermat number. For every $n \ge 2$ and every odd prime $p$ dividing $F_n$, we have
$2^{(p-1)/2} \equiv 1 \pmod{F_n}$. This result is due to Warren and Bray (1967).

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 2 (`integers-2026-A77-thm-2`), citing
Warren and Bray. -/
public theorem_wanted two_pow_half_modEq_one_fermatNumber {n p : ℕ} (hn : 2 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.fermatNumber n) :
    2 ^ ((p - 1) / 2) ≡ 1 [MOD Nat.fermatNumber n]

/-- **Squared prime factors of Fermat numbers via Wieferich primes and orders.** Let
$F_n = 2^{2^n} + 1$ be the $n$-th Fermat number. For every natural number $n$ and every odd prime
$p$, $p^2$ divides $F_n$ if and only if $p$ is a Wieferich prime (to base $2$) and the
multiplicative order of $2$ modulo $p$ is $2^{n+1}$.

This follows from the criterion that a prime $p$ dividing $F_n$ satisfies $p^2 \mid F_n$ exactly
when $2^{p-1} \equiv 1 \pmod{p^2}$, since an odd prime $p$ divides $F_n$ exactly when the order
of $2$ modulo $p$ is $2^{n+1}$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Theorem 5, Equation (11)
(`integers-2026-A77-thm-5`). -/
public theorem_wanted sq_dvd_fermatNumber_iff_wieferich_orderOf {n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ^ 2 ∣ Nat.fermatNumber n ↔ p.IsWieferichPrime ∧ orderOf (2 : ZMod p) = 2 ^ (n + 1)

/-- **Monotonicity of the number of prime factors of generalized Fermat numbers.** For natural
numbers $a$, $b$ and $n$ write $F_n(a, b) = a^{b^n} + 1$, and let $\Omega(N)$ be the number of
prime factors of $N$ counted with multiplicity. If $a, b \ge 2$ and $b$ is odd, then
$\Omega(F_n(a, b)) \le \Omega(F_m(a, b))$ for all natural numbers $n \le m$.

The source writes $\varphi_n(a, b)$ for $\Omega(F_n(a, b))$. Its open question on
$\varphi_n(2, 2)$ and its list of values of $\varphi_n(2, 2)$ are not stated here.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Corollary 1 (`integers-2026-A77-cor-1`). -/
public theorem_wanted monotone_cardFactors_pow_pow_add_one {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hbo : Odd b) :
    Monotone fun n : ℕ => ArithmeticFunction.cardFactors (a ^ b ^ n + 1)

/-- **Smaller iterated powers are not congruent to one.** Let $a, b, m \ge 2$ and $n \ge 1$ be
natural numbers with $a^{b^n} \not\equiv 1 \pmod m$. Then $a^{b^t} \not\equiv 1 \pmod m$ for every
natural number $t < n$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Lemma 2 (`integers-2026-A77-lem-2`). -/
public theorem_wanted not_pow_pow_modEq_one_of_lt {a b m n t : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hm : 2 ≤ m) (hn : 1 ≤ n) (h : ¬ a ^ b ^ n ≡ 1 [MOD m]) (ht : t < n) :
    ¬ a ^ b ^ t ≡ 1 [MOD m]

end

end MetaMathlibExt
