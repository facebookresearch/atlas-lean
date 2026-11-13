/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.Combinatorics.AP.Basic
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **Restricted twofold sumset of {0, 1, 2}.** In the integers, the restricted sumset
$2^{\wedge}\{0, 1, 2\}$, the set of sums of two distinct elements of $\{0, 1, 2\}$, equals
$\{1, 2, 3\}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1 (definition of `h^A`). -/
theorem restrictedSumset_two_zero_one_two :
    restrictedSumset 2 ({0, 1, 2} : Finset ℤ) = {1, 2, 3} := by
  decide

/-- **Sums with at least $r$ distinct terms.** Let $G$ be an additive commutative monoid, $A$ a
finite subset of $G$ and $h, r$ natural numbers. The sumset $h^{(\ge r)}A$ is the set of all sums
of $h$ elements of $A$, repetitions allowed, in which at least $r$ distinct elements occur, that
is, the elements $\sum_{a \in B} x_a a$ with $B \subseteq A$, $|B| \ge r$, positive integers
$x_a$ and $\sum_{a \in B} x_a = h$.

For $r = 1$ and $h \ge 1$ it is the $h$-fold sumset $hA$; for $r = h$ it is the restricted
sumset $h^{\wedge}A$ of sums of $h$ distinct elements of $A$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1, Definition 1. -/
def atLeastDistinctSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] (h r : ℕ)
    (A : Finset G) : Finset G :=
  ((A.sym h).filter fun s : Sym G h => r ≤ (s : Multiset G).toFinset.card).image
    fun s : Sym G h => (s : Multiset G).sum

/-- **Example of a sumset with at least two distinct terms.** In the integers, the set of sums of
three elements of $\{0, 1, 2\}$, repetitions allowed, in which at least two distinct elements
occur is $3^{(\ge 2)}\{0, 1, 2\} = \{1, 2, 3, 4, 5\}$; the sums $0$ and $6$ need a single
repeated term.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1, Definition 1. -/
theorem atLeastDistinctSumset_three_two_zero_one_two :
    atLeastDistinctSumset 3 2 ({0, 1, 2} : Finset ℤ) = {1, 2, 3, 4, 5} := by
  decide

/-- **Cauchy–Davenport theorem for $h$-fold sumsets.** Let $p$ be a prime, $A$ a nonempty subset
of $\mathbb{Z}/p\mathbb{Z}$ with $|A| = k$, and $h \ge 1$ a natural number. Then the $h$-fold
sumset $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ satisfies
$|hA| \ge \min(p,\ hk - h + 1)$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 1 (Cauchy–Davenport theorem) (`integers-2025-A12-thm-1`). -/
public theorem_wanted cauchy_davenport_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (h : ℕ) (hh : 1 ≤ h) :
    min p (h * A.card - h + 1) ≤ (h • A).card

/-- **Dias da Silva–Hamidoune theorem.** Let $p$ be a prime, $A$ a nonempty subset of
$\mathbb{Z}/p\mathbb{Z}$ with $|A| = k$, and $h$ a natural number with $1 \le h \le k$. Then the
restricted sumset $h^{\wedge}A$ of sums of $h$ distinct elements of $A$ satisfies
$|h^{\wedge}A| \ge \min(p,\ hk - h^2 + 1)$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 2 (Dias da Silva–Hamidoune theorem) (`integers-2025-A12-thm-2`). -/
public theorem_wanted dias_da_silva_hamidoune {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hA : A.Nonempty) (h : ℕ) (hh : 1 ≤ h) (hhk : h ≤ A.card) :
    min p (h * A.card - h ^ 2 + 1) ≤ (restrictedSumset h A).card

/-- **Vosper's theorem for iterated sumsets.** Let $p$ be a prime, let $A$ be a subset of the
cyclic group $\mathbb{Z}/p\mathbb{Z}$ with $k = |A| \ge 2$ elements, let $h \ge 2$ be an integer,
and let $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ be the $h$-fold sumset of $A$. If
$|hA| = hk - h + 1$ and $hk - h + 1 \le p - 2$, then $A$ is an arithmetic progression of
length $k$ in $\mathbb{Z}/p\mathbb{Z}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 3 (Vosper's theorem) (`integers-2025-A12-thm-3`). -/
public theorem_wanted vosper_nsmul {p : ℕ} (hp : p.Prime) (A : Finset (ZMod p))
    (hk : 2 ≤ A.card) (h : ℕ) (hh : 2 ≤ h) (hcard : (h • A).card = h * A.card - h + 1)
    (hsmall : h * A.card - h + 1 ≤ p - 2) :
    (A : Set (ZMod p)).IsAPOfLength A.card

/-- **Nathanson's inverse theorem for restricted sumsets.** Let $A$ be a finite set of integers
with $k = |A| \ge 5$ elements and let $h$ be an integer with $2 \le h \le k - 2$. Write
$h^{\wedge} A$ for the restricted sumset of $A$, the set of sums of $h$ distinct elements of
$A$. If $|h^{\wedge} A| = hk - h^2 + 1$, then $A$ is an arithmetic progression of length $k$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 4 (Nathanson) (`integers-2025-A12-thm-4`). -/
public theorem_wanted nathanson_restrictedSumset_inverse (A : Finset ℤ) (hk : 5 ≤ A.card)
    (h : ℕ) (hh : 2 ≤ h) (hhk : h ≤ A.card - 2)
    (hcard : (restrictedSumset h A).card = h * A.card - h ^ 2 + 1) :
    (A : Set ℤ).IsAPOfLength A.card

/-- **Freiman's $3k - 4$ theorem.** Let $A$ be a finite set of integers with $|A| = k \ge 3$,
$\min A = 0$ and $\gcd(A) = 1$, and let $b$ be a natural number. If
$|2A| = 2k - 1 + b \le 3k - 4$, where $2A = \{a + a' : a, a' \in A\}$, then $A$ is contained in
an arithmetic progression of length at most $k + b$.

Since $|2A| \ge 2k - 1$ always, taking $b$ to be a natural number loses nothing.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 5 (Freiman's `3k - 4` theorem) (`integers-2025-A12-thm-5`). -/
public theorem_wanted freiman_three_k_sub_four (A : Finset ℤ) (hk : 3 ≤ A.card) (h0 : 0 ∈ A)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hgcd : A.gcd id = 1) (b : ℕ)
    (hcard : (2 • A).card = 2 * A.card - 1 + b) (hb : 2 * A.card - 1 + b ≤ 3 * A.card - 4) :
    ∃ (P : Set ℤ) (l : ℕ), l ≤ A.card + b ∧ P.IsAPOfLength l ∧ (A : Set ℤ) ⊆ P

/-- **Plagne's theorem on the smallest iterated sumsets in cyclic groups.** Let $m$, $k$ and $h$
be natural numbers with $1 \le k \le m$ and $h \ge 1$. For a subset $A$ of
$\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$ let $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$
be its $h$-fold sumset. Then the minimum of $|hA|$ over all $k$-element subsets
$A \subseteq \mathbb{Z}_m$ is
$$\min\{(h \lceil k/d \rceil - h + 1)\, d : d \text{ a positive divisor of } m\}.$$

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 6 (Plagne) (`integers-2025-A12-thm-6`). -/
public theorem_wanted plagne_min_nsmul_card (m k h : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hh : 1 ≤ h) :
    sInf ((fun A : Finset (ZMod m) => (h • A).card) '' {A | A.card = k}) =
      sInf ((fun d => (h * ((k + d - 1) / d) - h + 1) * d) '' (m.divisors : Set ℕ))

/-- **Bajnok's lemma on subset sums in $\mathbb{Z}/d\mathbb{Z}$.** Let $d$ and $t$ be natural
numbers with $1 \le t \le d - 1$. Then every $\ell \in \mathbb{Z}/d\mathbb{Z}$ is the sum of the
elements of some $t$-element subset $L \subseteq \mathbb{Z}/d\mathbb{Z}$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 1 (Bajnok) (`integers-2025-A12-lem-1`). -/
public theorem_wanted exists_card_eq_sum_eq_zmod (d t : ℕ) (ht : 1 ≤ t) (htd : t ≤ d - 1)
    (ℓ : ZMod d) :
    ∃ L : Finset (ZMod d), L.card = t ∧ L.sum id = ℓ

/-- **Decomposition of sums with at least $r$ distinct terms.** Let $G$ be an abelian group, $A$
a nonempty finite subset of $G$, and $r, h$ natural numbers with $1 \le r \le |A|$ and $r \le h$.
Write $h^{(\ge r)}A$ for the set of sums of $h$ elements of $A$, repetitions allowed, in which at
least $r$ distinct elements occur, $(h - r)A$ for the set of sums of $h - r$ elements of $A$,
repetitions allowed (so $0A = \{0\}$), and $r^{\wedge}A$ for the restricted sumset of sums of
$r$ distinct elements of $A$. Then $h^{(\ge r)}A = (h - r)A + r^{\wedge}A$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 2, equation (5) (`integers-2025-A12-lem-2`). -/
public theorem_wanted atLeastDistinctSumset_eq_nsmul_add_restrictedSumset {G : Type*}
    [AddCommGroup G] [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (r h : ℕ) (hr : 1 ≤ r)
    (hrk : r ≤ A.card) (hrh : r ≤ h) :
    atLeastDistinctSumset h r A = (h - r) • A + restrictedSumset r A

/-- **Sharp lower bound for sums with at least $r$ distinct terms modulo a prime.** Let $p$ be a
prime, and for natural numbers $h, r$ and a finite set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ write
$h^{(\ge r)}A$ for the set of sums of $h$ elements of $A$, repetitions allowed, in which at least
$r$ distinct elements occur. If $A$ is nonempty with $|A| = k$, $1 \le r \le k$ and $r \le h$,
then $|h^{(\ge r)}A| \ge \min\{p,\ h(k - 1) - r(r - 1) + 1\}$. The bound is sharp: for all
natural numbers $k, r, h$ with $1 \le r \le k \le p$, $r \le h$ and
$h(k - 1) - r(r - 1) + 1 \le p$ there is a set $A \subseteq \mathbb{Z}/p\mathbb{Z}$ with
$|A| = k$ and $|h^{(\ge r)}A| = h(k - 1) - r(r - 1) + 1$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 9, equation (6) (`integers-2025-A12-thm-9`). -/
public theorem_wanted atLeastDistinctSumset_card_ge_zmod {p : ℕ} (hp : p.Prime) :
    (∀ (A : Finset (ZMod p)), A.Nonempty → ∀ r h : ℕ, 1 ≤ r → r ≤ A.card → r ≤ h →
      min p (h * (A.card - 1) - r * (r - 1) + 1) ≤ (atLeastDistinctSumset h r A).card) ∧
    ∀ k r h : ℕ, 1 ≤ r → r ≤ k → k ≤ p → r ≤ h → h * (k - 1) - r * (r - 1) + 1 ≤ p →
      ∃ A : Finset (ZMod p), A.card = k ∧
        (atLeastDistinctSumset h r A).card = h * (k - 1) - r * (r - 1) + 1

/-- **Inverse theorem for sums with at least $r$ distinct terms modulo a prime.** Let $p$ be a
prime, let $A \subseteq \mathbb{Z}/p\mathbb{Z}$ be a set with $|A| = k \ge 2$, and let $r, h$ be
natural numbers with $1 \le r \le k$ and $h \ge r + 2$. Write $h^{(\ge r)}A$ for the set of sums
of $h$ elements of $A$, repetitions allowed, in which at least $r$ distinct elements occur. If
$|h^{(\ge r)}A| = h(k - 1) - r(r - 1) + 1$ and $h(k - 1) - r(r - 1) + 1 \le p - 2$, then $A$ is
an arithmetic progression of length $k$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 11 (`integers-2025-A12-thm-11`). -/
public theorem_wanted atLeastDistinctSumset_inverse_zmod {p : ℕ} (hp : p.Prime)
    (A : Finset (ZMod p)) (hk : 2 ≤ A.card) (r h : ℕ) (hr : 1 ≤ r) (hrk : r ≤ A.card)
    (hh : r + 2 ≤ h)
    (hcard : (atLeastDistinctSumset h r A).card = h * (A.card - 1) - r * (r - 1) + 1)
    (hsmall : h * (A.card - 1) - r * (r - 1) + 1 ≤ p - 2) :
    (A : Set (ZMod p)).IsAPOfLength A.card

/-- **Lower bound and inverse theorem for sums with at least $r$ distinct terms in $\mathbb{Z}$.**
Let $A$ be a nonempty finite set of integers with $|A| = k$, and let $r, h$ be natural numbers
with $1 \le r \le k$, $r \le h$ and $h \ge 2$. Write $h^{(\ge r)}A$ for the set of sums of $h$
elements of $A$, repetitions allowed, in which at least $r$ distinct elements occur. Then
$|h^{(\ge r)}A| \ge h(k - 1) - r(r - 1) + 1$. If equality holds and either $k \ge 2$ and
$h \ge r + 2$, or $k \ge 5$, $2 \le r \le k - 2$ and $h \in \{r, r + 1\}$, then $A$ is an
arithmetic progression of length $k$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 12, equation (7) (`integers-2025-A12-thm-12`). -/
public theorem_wanted atLeastDistinctSumset_card_ge_int (A : Finset ℤ) (hA : A.Nonempty)
    (r h : ℕ) (hr : 1 ≤ r) (hrk : r ≤ A.card) (hrh : r ≤ h) (h2 : 2 ≤ h) :
    h * (A.card - 1) - r * (r - 1) + 1 ≤ (atLeastDistinctSumset h r A).card ∧
    ((atLeastDistinctSumset h r A).card = h * (A.card - 1) - r * (r - 1) + 1 →
      ((2 ≤ A.card ∧ r + 2 ≤ h) ∨
        (5 ≤ A.card ∧ 2 ≤ r ∧ r ≤ A.card - 2 ∧ (h = r ∨ h = r + 1))) →
      (A : Set ℤ).IsAPOfLength A.card)

/-- **Lev's lower bound for iterated sumsets.** Let $A$ be a finite set of integers with
$k = |A| \ge 3$ elements, smallest element $\min A = 0$ and $\gcd(A) = 1$. For $n \ge 1$ let
$nA = \{a_1 + \dots + a_n : a_1, \dots, a_n \in A\}$ be the $n$-fold sumset of $A$. Then for
every integer $h \ge 2$,
$$|hA| \ge |(h - 1)A| + \min\{\max A,\ h(k - 2) + 1\}.$$

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Theorem 13 (Lev) (`integers-2025-A12-thm-13`). -/
public theorem_wanted lev_nsmul_card_ge (A : Finset ℤ) (hk : 3 ≤ A.card) (h0 : 0 ∈ A)
    (hnonneg : ∀ a ∈ A, 0 ≤ a) (hgcd : A.gcd id = 1) (h : ℕ) (hh : 2 ≤ h) :
    (((h - 1) • A).card : ℤ) + min (A.max' ⟨0, h0⟩) ((h : ℤ) * (A.card - 2) + 1) ≤
      ((h • A).card : ℤ)

end

end MetaMathlibExt
