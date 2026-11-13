/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Modular generalizations of Schur numbers

Statements from Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62.

Following Chappelon, Revuelta Marchena, and Sanz Domínguez (*Modular Schur numbers*,
Electron. J. Combin. 20(2) (2013), #P61, reference [4] of the paper), a set `A` of integers is
`l`-sum-free modulo `m` if it contains no elements `x_1, …, x_l, y` (repetitions allowed) with
`x_1 + ⋯ + x_l ≡ y (mod m)`, and the generalized Schur number modulo `m`, `S_m(k, l)`, is the
largest `n` such that `{1, …, n}` admits a partition into `k` (possibly empty) classes that are
`l`-sum-free modulo `m`. Partitions are encoded as colorings by `Fin k`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sum-free sets modulo $m$.** For natural numbers $m$ and $l$, a set $A$ of integers is
$l$-sum-free modulo $m$ if there are no $x_1, \dots, x_l, y \in A$ (repetitions allowed) with
$x_1 + \dots + x_l \equiv y \pmod{m}$.

Source: J. Chappelon, M. P. Revuelta Marchena, M. I. Sanz Domínguez, *Modular Schur numbers*,
Electron. J. Combin. 20(2) (2013), Section 1.1, as used in Jourdan D'orville, Kai An Sim,
Kok Bin Wong, and Chee Kit Ho, *Modular Generalizations of Schur Numbers*, INTEGERS 25 (2025),
Article A62, Section 1. -/
def IsSumFreeMod (m l : ℕ) (A : Set ℤ) : Prop :=
  ∀ x : Fin l → ℤ, (∀ i, x i ∈ A) → ∀ y ∈ A, ¬ (∑ i, x i ≡ y [ZMOD m])

/-- **Sum-free partitions modulo $m$.** For natural numbers $m$, $k$, $l$ and $n$, the range
$\{1, \dots, n\}$ admits a partition into $k$ classes that are $l$-sum-free modulo $m$ if there
is a coloring $c$ of the natural numbers with $k$ colors such that, for each color $j$, the set
of integers $a$ with $1 \le a \le n$ and $c(a) = j$ is $l$-sum-free modulo $m$. Classes may be
empty; for $k = 0$ there is no coloring, so the property fails for every $n$, including $n = 0$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
def HasSumFreePartitionMod (m k l n : ℕ) : Prop :=
  ∃ c : ℕ → Fin k, ∀ j : Fin k,
    IsSumFreeMod m l {x : ℤ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ c a = j ∧ x = a}

/-- **Modular Schur number.** For natural numbers $m$, $k$ and $l$, the generalized Schur number
modulo $m$, written $S_m(k, l)$, is the largest natural number $n$ such that $\{1, \dots, n\}$
admits a partition into $k$ (possibly empty) classes that are each $l$-sum-free modulo $m$; it is
$0$ when there is no largest such $n$.

For $m \ge 1$ and $k \ge 1$ such a largest $n$ exists, since $n = 0$ is admissible and every
admissible $n$ is at most $m - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1. -/
noncomputable def modularSchurNumber (m k l : ℕ) : ℕ :=
  sSup {n : ℕ | HasSumFreePartitionMod m k l n}

/-- **The empty range has a sum-free partition.** For all natural numbers $m$, $l$ and
$k \ge 1$, the empty range $\{1, \dots, 0\}$ admits a partition into $k$ classes that are
$l$-sum-free modulo $m$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1
(`0 ≤ S_m(k, l)`). -/
theorem hasSumFreePartitionMod_zero (m k l : ℕ) : HasSumFreePartitionMod m (k + 1) l 0 := by
  refine ⟨fun _ => 0, fun j x _ y hy => ?_⟩
  obtain ⟨a, h1, h2, -⟩ := hy
  omega

/-- **Sets containing a multiple of the modulus are not sum-free.** Let $m$ and $l$ be natural
numbers and let $A$ be a set of integers. If $A$ contains an integer $a$ divisible by $m$, then
$A$ is not $l$-sum-free modulo $m$: the sum of $l$ copies of $a$ is congruent to $a$ modulo $m$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Section 1
(the bound `S_m(k, l) ≤ m - 1`). -/
theorem not_isSumFreeMod_of_dvd_mem (m l : ℕ) {A : Set ℤ} {a : ℤ} (ha : a ∈ A)
    (hm : (m : ℤ) ∣ a) : ¬ IsSumFreeMod m l A := by
  intro h
  refine h (fun _ => a) (fun _ => ha) a ha ?_
  rw [Int.modEq_iff_dvd]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : a - (l : ℤ) * a = (1 - l) * a := by ring
  rw [this]
  exact dvd_mul_of_dvd_right hm _

/-- **$\{1\}$ is $2$-sum-free modulo $3$.** The singleton $\{1\}$ is $2$-sum-free modulo $3$,
since $1 + 1 \not\equiv 1 \pmod{3}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 2 context. -/
theorem isSumFreeMod_three_two_singleton_one : IsSumFreeMod 3 2 {1} := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst hy
  rw [Fin.sum_univ_two, hx 0, hx 1]
  decide

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

/-- **Modular Schur numbers modulo an even number.** Let $k$, $l$ and $n$ be natural numbers with
$k \ge 2$, $n \ge 2$, $l \ge 1$ and $l \not\equiv 1 \pmod{2n}$, and let $S_{2n}(k, l)$ be the
generalized Schur number modulo $2n$. If $l \equiv n + 1 \pmod{2n}$, then $S_{2n}(k, l) = 1$;
otherwise $S_{2n}(k, l) \ge 2$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 4
(`integers-2025-A62-cor-4`). -/
public theorem_wanted modularSchurNumber_two_mul (k l n : ℕ) (hk : 2 ≤ k) (hn : 2 ≤ n)
    (hl : 0 < l) (hl1 : ¬ l ≡ 1 [MOD 2 * n]) :
    (l ≡ n + 1 [MOD 2 * n] → modularSchurNumber (2 * n) k l = 1) ∧
      (¬ l ≡ n + 1 [MOD 2 * n] → 2 ≤ modularSchurNumber (2 * n) k l)

/-- **Modular Schur numbers attaining $m - 1$.** Let $l \ge 2$ and $m \ge 2$ be natural numbers
such that $l \not\equiv 1 \pmod{d}$ for every divisor $d \ne 1$ of $m$, and let $k \ge m - 1$.
Then the generalized Schur number $S_m(k, l)$, the largest $n$ such that $\{1, \dots, n\}$
admits a partition into $k$ classes that are $l$-sum-free modulo $m$, equals $m - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 5
(`integers-2025-A62-cor-5`). -/
public theorem_wanted modularSchurNumber_eq_sub_one (m k l : ℕ) (hl : 2 ≤ l) (hm : 2 ≤ m)
    (hd : ∀ d : ℕ, d ∣ m → d ≠ 1 → ¬ l ≡ 1 [MOD d]) (hk : m - 1 ≤ k) :
    modularSchurNumber m k l = m - 1

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

/-- **Modular Schur numbers modulo a prime power for many classes.** Let $p$ be a prime, let $i$
and $l$ be positive integers with $l \not\equiv 1 \pmod p$, and let $k$ be a natural number with
$k \ge p^i - 1$. Then the generalized Schur number modulo $p^i$ satisfies
$S_{p^i}(k, l) = p^i - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Corollary 7
(`integers-2025-A62-cor-7`). -/
public theorem_wanted modularSchurNumber_prime_pow_eq (p i k l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (hlp : ¬ l ≡ 1 [MOD p]) (hk : p ^ i - 1 ≤ k) :
    modularSchurNumber (p ^ i) k l = p ^ i - 1

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

/-- **Singletons are sum-free modulo a prime power.** Let $p$ be a prime, let $i$ and $l$ be
positive integers with $l \not\equiv 1 \pmod{p}$, and let $a$ be a natural number not divisible
by $p^i$. Then the singleton $\{a\}$ is $l$-sum-free modulo $p^i$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 1
(`integers-2025-A62-lem-1`). -/
public theorem_wanted isSumFreeMod_singleton_prime_pow (p a i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : 0 < l) (ha : ¬ p ^ i ∣ a) (hlp : ¬ l ≡ 1 [MOD p]) :
    IsSumFreeMod (p ^ i) l {(a : ℤ)}

/-- **Elements of a sum-free pair are congruent modulo $p$.** Let $p$ be a prime, let $i$ be a
positive integer, and let $l$ be a natural number with $l \ge p^i - 1$ and
$l \not\equiv 1 \pmod{p}$. If $a$ and $b$ are natural numbers such that $\{a, b\}$ is
$l$-sum-free modulo $p^i$, then $a \equiv b \pmod{p}$.

Since subsets of $l$-sum-free sets are $l$-sum-free, the hypothesis says exactly that $a$ and
$b$ lie in a common $l$-sum-free set modulo $p^i$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Lemma 2, part 1
(`integers-2025-A62-lem-2`). -/
public theorem_wanted modEq_of_isSumFreeMod_pair (p a b i l : ℕ) (hp : p.Prime) (hi : 0 < i)
    (hl : p ^ i - 1 ≤ l) (hlp : ¬ l ≡ 1 [MOD p])
    (hab : IsSumFreeMod (p ^ i) l {(a : ℤ), (b : ℤ)}) : a ≡ b [MOD p]

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

/-- **Solutions of a linear congruence.** Let $a$ and $b$ be integers, let $m$ be a positive
integer, and let $d = \gcd(a, m)$. The congruence $a x \equiv b \pmod{m}$ has an integer
solution if and only if $d \mid b$. If $d \mid b$, then exactly $d$ of the numbers
$x \in \{0, 1, \dots, m - 1\}$ are solutions. Moreover, if $x_0$ is a solution, then an integer
$x$ is a solution if and only if $x \equiv x_0 + u \cdot (m / d) \pmod{m}$ for some integer $u$
with $0 \le u \le d - 1$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 3, quoting a
textbook result ([3]) (`integers-2025-A62-thm-3`). -/
public theorem_wanted linear_congruence_solutions (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    ((∃ x : ℤ, a * x ≡ b [ZMOD m]) ↔ (Int.gcd a m : ℤ) ∣ b) ∧
      ((Int.gcd a m : ℤ) ∣ b →
        ((Finset.range m).filter fun x : ℕ => a * x ≡ b [ZMOD m]).card = Int.gcd a m) ∧
      ∀ x₀ : ℤ, a * x₀ ≡ b [ZMOD m] → ∀ x : ℤ,
        (a * x ≡ b [ZMOD m] ↔
          ∃ u : ℕ, u < Int.gcd a m ∧ x ≡ x₀ + u * ((m : ℤ) / Int.gcd a m) [ZMOD m])

/-- **When a singleton set is sum-free.** Let $a$, $l$ and $m$ be natural numbers with
$l \ge 1$, $m \ge 1$ and $m \nmid a$, and let $d = \gcd(a, m)$. If $d = 1$, then $\{a\}$ is not
$l$-sum-free modulo $m$ if and only if $l \equiv 1 \pmod{m}$. If $d > 1$, then $\{a\}$ is not
$l$-sum-free modulo $m$ if and only if $l \equiv 1 \pmod{m/d}$.

Source: Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular
Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 4
(`integers-2025-A62-thm-4`). -/
public theorem_wanted not_isSumFreeMod_singleton_iff (a l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (ha : ¬ m ∣ a) :
    (Nat.gcd a m = 1 → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m])) ∧
      (1 < Nat.gcd a m → (¬ IsSumFreeMod m l {(a : ℤ)} ↔ l ≡ 1 [MOD m / Nat.gcd a m]))

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
