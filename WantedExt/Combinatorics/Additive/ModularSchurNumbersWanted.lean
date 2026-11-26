/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Additive.LinearCongruenceSolutions
public import MathlibExt.Combinatorics.Additive.ModularSchurNumbers
public import MathlibExt.Combinatorics.Additive.SingletonSumFreeMod

/-!
# Wanted results on modular Schur numbers

Further statements from *Modular Generalizations of Schur Numbers*.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **When the singleton $\{1\}$ is sum-free.** Let $m \ge 1$ and $l$ be natural
numbers. The singleton $\{1\}$ is not $l$-sum-free modulo $m$ if and only if
$l \equiv 1 \pmod{m}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 1
(`integers-2025-A62-cor-1`). -/
public theorem_wanted not_isSumFreeMod_singleton_one_iff (m l : ℕ) (hm : 0 < m) :
    ¬ IsSumFreeMod m l {1} ↔ l ≡ 1 [MOD m]

/-- **Vanishing of modular Schur numbers.** Let $m$, $k$ and $l$ be positive integers. The
generalized Schur number $S_m(k, l)$, the largest $n$ such that $\{1, \dots, n\}$ admits a
partition into $k$ classes that are $l$-sum-free modulo $m$, equals $0$ if and only if
$l \equiv 1 \pmod{m}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 2
(`integers-2025-A62-cor-2`). -/
public theorem_wanted modularSchurNumber_eq_zero_iff (m k l : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hl : 0 < l) : modularSchurNumber m k l = 0 ↔ l ≡ 1 [MOD m]

/-- **Congruence upper bound for modular Schur numbers.** Let $m$, $k$, $l$ and $a$ be natural
numbers with $k \ge 1$, $l \ge 1$ and $1 \le a \le m - 1$, and let $d = \gcd(a, m)$. If
$l \equiv 1 \pmod{m/d}$, then the generalized Schur number $S_m(k, l)$ modulo $m$ satisfies
$S_m(k, l) < a$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 3
(`integers-2025-A62-cor-3`). -/
public theorem_wanted modularSchurNumber_lt_of_modEq (m k l a : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ha : 0 < a) (ham : a ≤ m - 1) (hla : l ≡ 1 [MOD m / Nat.gcd a m]) :
    modularSchurNumber m k l < a

/-- **Lower bound for modular Schur numbers modulo a prime power.** Let $p$ be a prime, let $i$
and $l$ be positive integers with $l \not\equiv 1 \pmod{p}$, and let $1 \le k \le p - 1$. Then
the generalized Schur number $S_{p^i}(k, l)$, the largest $n$ such that $\{1, \dots, n\}$ admits
a partition into $k$ classes that are $l$-sum-free modulo $p^i$, is at least $k$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 6
(`integers-2025-A62-cor-6`). -/
public theorem_wanted le_modularSchurNumber_prime_pow (p i k l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (hlp : ¬ l ≡ 1 [MOD p]) (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    k ≤ modularSchurNumber (p ^ i) k l

/-- **Modular Schur numbers modulo a prime.** Let $p$ be a prime and let $l$ be a positive integer
with $l \ge p - 1$ and $l \not\equiv 1 \pmod p$. Then the generalized Schur number modulo $p$
satisfies $S_p(k, l) = k$ for every natural number $k$ with $1 \le k \le p - 1$, and
$S_p(k, l) = p - 1$ for every natural number $k \ge p - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 8
(`integers-2025-A62-cor-8`). -/
public theorem_wanted modularSchurNumber_prime (p l : ℕ) (hp : p.Prime) (hl : 0 < l)
    (hlp1 : p - 1 ≤ l) (hlp : ¬ l ≡ 1 [MOD p]) :
    (∀ k, 1 ≤ k → k ≤ p - 1 → modularSchurNumber p k l = k) ∧
      (∀ k, p - 1 ≤ k → modularSchurNumber p k l = p - 1)

/-- **Modular Schur numbers modulo $2$.** For all positive integers $k$ and $l$, the modular
Schur number $S_2(k, l)$ equals $0$ when $l$ is odd and equals $1$ when $l$ is even.

The source quotes this result from its reference [4], Chappelon, Revuelta Marchena and Sanz
Domínguez, *Modular Schur numbers* (2013).

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 1
(`integers-2025-A62-thm-1`). -/
public theorem_wanted modularSchurNumber_two (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 2] → modularSchurNumber 2 k l = 0) ∧
      (l ≡ 0 [MOD 2] → modularSchurNumber 2 k l = 1)

/-- **Modular Schur numbers modulo 3.** Let $k$ and $l$ be positive integers and let $S_3(k, l)$
be the generalized Schur number modulo $3$. If $l \equiv 1 \pmod 3$, then $S_3(k, l) = 0$.
Otherwise $S_3(1, l) = 1$, and $S_3(k, l) = 2$ for every $k \ge 2$.

The paper quotes this result from Chappelon, Revuelta Marchena, and Sanz Domínguez,
*Modular Schur numbers* (2013).

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 2
(`integers-2025-A62-thm-2`). -/
public theorem_wanted modularSchurNumber_three (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 3] → modularSchurNumber 3 k l = 0) ∧
      (¬ l ≡ 1 [MOD 3] →
        (k = 1 → modularSchurNumber 3 k l = 1) ∧ (2 ≤ k → modularSchurNumber 3 k l = 2))

/-- **When the one-class modular Schur number equals one.** Let $l$ and $m$ be natural numbers with
$l \ge 2$, $m \ge 2$ and $l \not\equiv 1 \pmod m$. Then the generalized Schur number $S_m(1, l)$
modulo $m$ equals $1$ if and only if $l = 2$ or $2l \ge m + 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 5
(`integers-2025-A62-thm-5`). -/
public theorem_wanted modularSchurNumber_one_eq_one_iff (l m : ℕ) (hl : 2 ≤ l) (hm : 2 ≤ m)
    (hlm : ¬ l ≡ 1 [MOD m]) :
    modularSchurNumber m 1 l = 1 ↔ l = 2 ∨ m + 1 ≤ 2 * l

/-- **Modular Schur numbers modulo 4.** Let $k$ and $l$ be positive integers and let $S_4(k, l)$
be the generalized Schur number modulo $4$. If $l \equiv 1 \pmod 4$, then $S_4(k, l) = 0$.
Otherwise, if $k = 1$, or if $k \ge 2$ and $l \equiv 3 \pmod 4$, then $S_4(k, l) = 1$; and if
$k \ge 2$ and $l \equiv 0$ or $2 \pmod 4$, then $S_4(k, l) = 3$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 6
(`integers-2025-A62-thm-6`). -/
public theorem_wanted modularSchurNumber_four (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 4] → modularSchurNumber 4 k l = 0) ∧
      (¬ l ≡ 1 [MOD 4] →
        ((k = 1 ∨ (2 ≤ k ∧ l ≡ 3 [MOD 4])) → modularSchurNumber 4 k l = 1) ∧
        ((2 ≤ k ∧ (l ≡ 0 [MOD 4] ∨ l ≡ 2 [MOD 4])) → modularSchurNumber 4 k l = 3))

/-- **Modular Schur numbers modulo 6.** Let $k$ and $l$ be positive integers and let $S_6(k, l)$
be the generalized Schur number modulo $6$. If $l \equiv 1 \pmod 6$, then $S_6(k, l) = 0$.
Otherwise $S_6(k, l) = 1$ if $k = 1$ and $l \ne 3$, or $k \ge 2$ and $l \equiv 4 \pmod 6$;
$S_6(k, l) = 2$ if $k = 1$ and $l = 3$, or $k \ge 2$ and $l \equiv 3$ or $5 \pmod 6$;
$S_6(k, l) = 3$ if $k = 2$, $l \equiv 0$ or $2 \pmod 6$, and $l \ge 6$; $S_6(k, l) = 4$ if
$k = l = 2$; and $S_6(k, l) = 5$ if $k \ge 3$ and $l \equiv 0$ or $2 \pmod 6$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 7
(`integers-2025-A62-thm-7`). -/
public theorem_wanted modularSchurNumber_six (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 6] → modularSchurNumber 6 k l = 0) ∧
      (¬ l ≡ 1 [MOD 6] →
        (((k = 1 ∧ l ≠ 3) ∨ (2 ≤ k ∧ l ≡ 4 [MOD 6])) → modularSchurNumber 6 k l = 1) ∧
        (((k = 1 ∧ l = 3) ∨ (2 ≤ k ∧ (l ≡ 3 [MOD 6] ∨ l ≡ 5 [MOD 6]))) →
          modularSchurNumber 6 k l = 2) ∧
        ((k = 2 ∧ (l ≡ 0 [MOD 6] ∨ l ≡ 2 [MOD 6]) ∧ 6 ≤ l) → modularSchurNumber 6 k l = 3) ∧
        ((k = 2 ∧ l = 2) → modularSchurNumber 6 k l = 4) ∧
        ((3 ≤ k ∧ (l ≡ 0 [MOD 6] ∨ l ≡ 2 [MOD 6])) → modularSchurNumber 6 k l = 5))

/-- **Modular Schur numbers modulo 5.** Let $k$ and $l$ be positive integers and let $S_5(k, l)$
be the generalized Schur number modulo $5$. If $l \equiv 1 \pmod 5$, then $S_5(k, l) = 0$.
Otherwise $S_5(1, l) = 1$; if $k \in \{2, 3\}$ and $l \ne 2$, then $S_5(k, l) = k$; and if
$k \in \{2, 3\}$ and $l = 2$, or if $k \ge 4$, then $S_5(k, l) = 4$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 9
(`integers-2025-A62-thm-9`). -/
public theorem_wanted modularSchurNumber_five (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 5] → modularSchurNumber 5 k l = 0) ∧
      (¬ l ≡ 1 [MOD 5] →
        (k = 1 → modularSchurNumber 5 k l = 1) ∧
        (((k = 2 ∨ k = 3) ∧ l ≠ 2) → modularSchurNumber 5 k l = k) ∧
        ((((k = 2 ∨ k = 3) ∧ l = 2) ∨ 4 ≤ k) → modularSchurNumber 5 k l = 4))

/-- **Modular Schur numbers modulo 7.** Let $k$ and $l$ be positive integers and let $S_7(k, l)$
be the generalized Schur number modulo $7$. If $l \equiv 1 \pmod 7$, then $S_7(k, l) = 0$.
Otherwise $S_7(k, l) = 1$ if $k = 1$ and $l \ne 3$; $S_7(k, l) = 2$ if $k = 1$ and $l = 3$, or
$k = 2$ and $l \ge 4$; $S_7(k, l) = 3$ if $k = 2$ and $l \in \{2, 3\}$, or $k = 3$ and $l \ge 5$;
$S_7(k, l) = 4$ if $k = 4$ and $l \ge 5$; $S_7(k, l) = 5$ if $k = 3$ and $l = 3$, or $k = 5$ and
$l \ge 5$; and $S_7(k, l) = 6$ if $k = 3$ and $l \in \{2, 4\}$, or $k \in \{4, 5\}$ and
$2 \le l \le 4$, or $k \ge 6$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 10
(`integers-2025-A62-thm-10`). -/
public theorem_wanted modularSchurNumber_seven (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    (l ≡ 1 [MOD 7] → modularSchurNumber 7 k l = 0) ∧
      (¬ l ≡ 1 [MOD 7] →
        ((k = 1 ∧ l ≠ 3) → modularSchurNumber 7 k l = 1) ∧
        (((k = 1 ∧ l = 3) ∨ (k = 2 ∧ 4 ≤ l)) → modularSchurNumber 7 k l = 2) ∧
        (((k = 2 ∧ (l = 2 ∨ l = 3)) ∨ (k = 3 ∧ 5 ≤ l)) → modularSchurNumber 7 k l = 3) ∧
        ((k = 4 ∧ 5 ≤ l) → modularSchurNumber 7 k l = 4) ∧
        (((k = 3 ∧ l = 3) ∨ (k = 5 ∧ 5 ≤ l)) → modularSchurNumber 7 k l = 5) ∧
        (((k = 3 ∧ (l = 2 ∨ l = 4)) ∨ ((k = 4 ∨ k = 5) ∧ 2 ≤ l ∧ l ≤ 4) ∨ 6 ≤ k) →
          modularSchurNumber 7 k l = 6))

end

end MetaMathlibExt
