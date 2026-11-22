/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# The union of two arithmetic progressions is not an MSTD set

Statements from Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic
Progressions with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026),
Article A58.

A finite set `A ⊆ ℝ` is an MSTD (more sums than differences) set when `|A + A| > |A - A|`. The
paper normalizes the first progression to `I_n = {0, 1, …, n - 1}` and the second to
`J(x, m, d) = {x + i d : i ∈ [0, m]}`. The paper's `ℕ` is the positive integers; membership in
`ℕ` is written here as `y ∈ Set.range ((↑) : ℕ → ℝ)`, which also admits `0`. Where this is used,
either the hypotheses already exclude `0` or the claim holds for every integer value; the one
case where `0` matters, `d ∈ ℚ ∖ ℕ` in Lemma 19 (i), is written with positive integers.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- **Initial integer interval.** For a natural number $n$, $I_n = \{0, 1, \ldots, n - 1\}$ is
the set of the first $n$ natural numbers, viewed as a finite set of real numbers; $I_0$ is empty.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realIntervalSet (n : ℕ) : Finset ℝ :=
  (Finset.range n).image fun i : ℕ => (i : ℝ)

/-- **Size of the interval $I_n$.** For every natural number $n$, the set
$I_n = \{0, 1, \dots, n - 1\}$ of real numbers has exactly $n$ elements.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realIntervalSet (n : ℕ) : (realIntervalSet n).card = n := by
  rw [realIntervalSet, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- **Finite arithmetic progression.** For a real number $x$, a natural number $m$ and a real
number $d$, $J(x, m, d)$ is the finite set of real numbers
$\{x + i d : i = 0, 1, \ldots, m\}$, that is, $x, x + d, \ldots, x + m d$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
noncomputable def realAPSet (x : ℝ) (m : ℕ) (d : ℝ) : Finset ℝ :=
  (Finset.range (m + 1)).image fun i : ℕ => x + i * d

/-- **Size of the progression $J(x, m, d)$.** For a real number $x$, a natural number $m$ and a
real number $d \ne 0$, the progression $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$ has exactly
$m + 1$ elements.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem card_realAPSet (x : ℝ) (m : ℕ) {d : ℝ} (hd : d ≠ 0) :
    (realAPSet x m d).card = m + 1 := by
  rw [realAPSet, Finset.card_image_of_injective, Finset.card_range]
  intro i j h
  have : (i : ℝ) * d = j * d := by simpa using h
  exact_mod_cast mul_right_cancel₀ hd this

/-- **MSTD set.** A finite set $A$ of real numbers is an *MSTD set* (more sums than differences)
when its difference set has fewer elements than its sumset: $|A - A| < |A + A|$, where
$A + A = \{a + b : a, b \in A\}$ and $A - A = \{a - b : a, b \in A\}$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
def IsMSTDSet (A : Finset ℝ) : Prop :=
  (A - A).card < (A + A).card

/-- **A single point is not an MSTD set.** For every real number $a$, the set $\{a\}$ is not an
MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58,
Section 1. -/
theorem not_isMSTDSet_singleton (a : ℝ) : ¬ IsMSTDSet {a} := by
  simp [IsMSTDSet]

/-- **The union of two separated arithmetic progressions is not an MSTD set.** For real numbers
$x, d$ and a natural number $m$, write $J(x, m, d) = \{x + i d : i = 0, 1, \ldots, m\}$. Let
$a, b, d_1, d_2$ be real numbers with $d_1 > 0$ and $d_2 > 0$, and let $m_1, m_2$ be natural
numbers with $a + m_1 d_1 < b$, so that the largest element of $J(a, m_1, d_1)$ is less than the
smallest element of $J(b, m_2, d_2)$. Then $J(a, m_1, d_1) \cup J(b, m_2, d_2)$ is not an MSTD
set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Theorem 1
(`integers-2026-A58-thm-1`). -/
public theorem_wanted not_isMSTDSet_union_two_ap (a b d₁ d₂ : ℝ) (m₁ m₂ : ℕ) (hd₁ : 0 < d₁)
    (hd₂ : 0 < d₂)
    (hlt : a + m₁ * d₁ < b) :
    ¬ IsMSTDSet (realAPSet a m₁ d₁ ∪ realAPSet b m₂ d₂)

/-- **Interval plus integer progression starting in $[n + 1, 2n - 2]$ is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x$ with
$n + 1 \le x \le 2n - 2$, the set $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 1
(`integers-2026-A58-lem-1`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_le_two_mul_sub_two (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx₁ : n + 1 ≤ x) (hx₂ : x ≤ 2 * n - 2) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Interval plus integer progression starting at $2n - 1$ or later is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x \ge 2n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 2
(`integers-2026-A58-lem-2`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_two_mul_sub_one_le (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : 2 * n - 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Interval plus integer progression starting after the interval is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x > n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 3
(`integers-2026-A58-lem-3`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_lt (n m d x : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hd : 2 ≤ d)
    (hx : n - 1 < x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **Interval plus irrational-step progression with natural start is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$ and $x \ge n + 1$, and a positive
irrational real number $d$, the set $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 4
(`integers-2026-A58-lem-4`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_diff (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hirr : Irrational d)
    (hd : 0 < d) (hx : n + 1 ≤ x) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **An interval and a later natural-start progression with few terms or large step are not MSTD.**
Let $n \ge 3$, $m$ and $x$ be natural numbers with $x \ge n + 1$, and let $d = s + p/q$, where
$s, p, q$ are natural numbers with $0 < p < q$ and $\gcd(p, q) = 1$. Suppose that either
$2 \le m \le q - 1$, or $m \ge q$ and $qd > n - 1$. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 5
(`integers-2026-A58-lem-5`). -/
public theorem_wanted not_isMSTDSet_intervalAP_rat_diff (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n) (s p q : ℕ)
    (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : n + 1 ≤ x) (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **An interval and a later progression with natural start and small step are not MSTD.** Let
$n \ge 3$, $m$ and $x$ be natural numbers with $x \ge n + 1$, and let $d = s + p/q$, where
$s, p, q$ are natural numbers with $0 < p < q$ and $\gcd(p, q) = 1$. Suppose that $m \ge q$ and
$qd \le n - 1$. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 6
(`integers-2026-A58-lem-6`). -/
public theorem_wanted not_isMSTDSet_intervalAP_rat_diff_of_le (n m x : ℕ) (d : ℝ) (hn : 3 ≤ n)
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hqd : q * d ≤ (n : ℝ) - 1) (hx : n + 1 ≤ x) (hm : q ≤ m) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m d)

/-- **Interval plus irrational-step progression avoiding the naturals is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. Let $n \ge 3$ and $m$ be natural numbers, $d$ a positive irrational real number
and $x > n - 1$ a real number such that none of $x + id$ for $i = 0, 1, \dots, m$ is a natural
number. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 7
(`integers-2026-A58-lem-7`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_of_forall_not_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (hirr : Irrational d) (hd : 0 < d) (hx : (n : ℝ) - 1 < x)
    (hnat : ∀ i ≤ m, x + i * d ∉ Set.range ((↑) : ℕ → ℝ)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **At most one nonnegative integer point on a progression with irrational difference.** Let $x$
and $d$ be real numbers with $d$ irrational. If $i$ and $j$ are natural numbers such that $x + id$
and $x + jd$ are both nonnegative integers, then $i = j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 8
(`integers-2026-A58-lem-8`). -/
public theorem_wanted eq_of_add_mul_irrational_mem_nat (x d : ℝ) (hirr : Irrational d) (i j : ℕ)
    (hi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j

/-- **Interval plus irrational-step progression meeting the naturals is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. Let $n \ge 3$ and $m$ be natural numbers, $d$ a positive irrational real number
and $x > n - 1$ a real number that is not a natural number, and suppose that $x + jd$ is a
natural number for some integer $j$ with $1 \le j \le m$. Then $I_n \cup J(x, m, d)$ is not
an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 9
(`integers-2026-A58-lem-9`). -/
public theorem_wanted not_isMSTDSet_intervalAP_irrational_of_exists_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (hirr : Irrational d) (hd : 0 < d) (hx : (n : ℝ) - 1 < x)
    (hnat : ∃ j, 1 ≤ j ∧ j ≤ m ∧ x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **An interval and a later rational-step progression with no integer term are not MSTD.** Let
$n \ge 3$ and $m$ be natural numbers, let $x > n - 1$ be a real number that is not a natural
number, and let $d = s + p/q$, where $s, p, q$ are natural numbers with $0 < p < q$ and
$\gcd(p, q) = 1$. Suppose that $x + id$ is not a natural number for any natural number $i \le m$,
and that either $2 \le m \le q - 1$, or $m \ge q$ and $qd > n - 1$. Write
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 10
(`integers-2026-A58-lem-10`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_forall_not_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : (n : ℝ) - 1 < x) (hnat : ∀ i ≤ m, x + i * d ∉ Set.range ((↑) : ℕ → ℝ))
    (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Uniqueness of a nonnegative integer point for a rational difference.** Let $x$ be a real
number, let $s, p, q$ be natural numbers with $0 < p < q$ and $\gcd(p, q) = 1$, and let
$d = s + p/q$. If $i, j \in \{1, \dots, q - 1\}$ and $x + id$ and $x + jd$ are both nonnegative
integers, then $i = j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 11
(`integers-2026-A58-lem-11`). -/
public theorem_wanted eq_of_add_mul_rat_mem_nat (x d : ℝ) (s p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q) (i j : ℕ)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ q - 1) (hj₁ : 1 ≤ j) (hj₂ : j ≤ q - 1)
    (hxi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hxj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j

/-- **An interval and a later rational-step progression with an integer term are not MSTD.** Let
$n \ge 3$ and $m$ be natural numbers, let $x > n - 1$ be a real number that is not a natural
number, and let $d = s + p/q$, where $s, p, q$ are natural numbers with $0 < p < q$ and
$\gcd(p, q) = 1$. Suppose that $x + jd$ is a natural number for some natural number $j$ with
$1 \le j \le q - 1$, and that either $2 \le m \le q - 1$, or $m \ge q$ and $qd > n - 1$. Write
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 12
(`integers-2026-A58-lem-12`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_exists_nat (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hx : (n : ℝ) - 1 < x) (hnat : ∃ j, 1 ≤ j ∧ j ≤ q - 1 ∧ x + j * d ∈ Set.range ((↑) : ℕ → ℝ))
    (hm : (2 ≤ m ∧ m ≤ q - 1) ∨ (q ≤ m ∧ (n : ℝ) - 1 < q * d)) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **An interval and a later progression with non-integer start and small step are not MSTD.**
Let $n \ge 3$ and $m$ be natural numbers, let $x > n - 1$ be a real number that is not a natural
number, and let $d = s + p/q$, where $s, p, q$ are natural numbers with $0 < p < q$ and
$\gcd(p, q) = 1$. Suppose that $m \ge q$ and $qd \le n - 1$. Write
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 13
(`integers-2026-A58-lem-13`). -/
public theorem_wanted not_isMSTDSet_intervalAP_real_rat_diff_of_le (n m : ℕ) (x d : ℝ) (hn : 3 ≤ n)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ))
    (s p q : ℕ) (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q)
    (hqd : q * d ≤ (n : ℝ) - 1) (hx : (n : ℝ) - 1 < x) (hm : q ≤ m) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Interval plus integer progression starting inside the interval is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. For natural numbers $n \ge 3$, $m \ge 2$, $d \ge 2$ and $x \le n - 1$, the set
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 14
(`integers-2026-A58-lem-14`). -/
public theorem_wanted not_isMSTDSet_intervalAP_nat_of_le_sub_one (n m d x : ℕ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : 2 ≤ d)
    (hx : x ≤ n - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet (x : ℝ) m (d : ℝ))

/-- **An interval and an overlapping progression with small integer step are not MSTD.** Let
$n \ge 3$, $m \ge 2$ and $d$ be natural numbers with $2 \le d \le n - 1$, and let $x$ be a real
number with $0 < x < n - 1$ such that either $x$ is irrational or $x = s + p/q$ for natural
numbers $s, p, q$ with $0 < p < q$, $q \ne 2$ and $\gcd(p, q) = 1$. Write
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 15
(`integers-2026-A58-lem-15`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_den_ne_two (n m d : ℕ) (x : ℝ)
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hd₁ : 2 ≤ d)
    (hd₂ : d ≤ n - 1)
    (hxform : Irrational x ∨ ∃ s p q : ℕ, 0 < p ∧ p < q ∧ q ≠ 2 ∧ Nat.Coprime p q ∧
      x = s + (p : ℝ) / q)
    (hx₀ : 0 < x) (hx₁ : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **Interval plus integer-step progression with half-integer start is not MSTD.** Let
$I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. Let $n \ge 3$, $m \ge 2$, $s$ and $d$ be natural numbers with
$2 \le d \le n - 1$, and let $x = s + 1/2$. If $x < n - 1$, then $I_n \cup J(x, m, d)$ is not an
MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 16
(`integers-2026-A58-lem-16`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_half (n m d s : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd₁ : 2 ≤ d)
    (hd₂ : d ≤ n - 1) (hxs : x = s + 1 / 2) (hx : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **Interval plus progression with non-integer start and integer step at least $n$ is not MSTD.**
Let $n \ge 3$, $m \ge 2$ and $d \ge n$ be natural numbers, and let $x$ be a real number with
$0 < x < n - 1$ that is not a natural number. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 17
(`integers-2026-A58-lem-17`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_large_diff (n m d : ℕ) (x : ℝ) (hn : 3 ≤ n)
    (hm : 2 ≤ m) (hd : n ≤ d)
    (hxN : x ∉ Set.range ((↑) : ℕ → ℝ)) (hx₀ : 0 < x) (hx₁ : x < (n : ℝ) - 1) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m (d : ℝ))

/-- **An interval and an overlapping progression with incompatible start and step are not MSTD.**
Let $n \ge 3$ and $m \ge 2$ be natural numbers, and let $x$ and $d$ be real numbers with
$0 < x < n - 1$. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Suppose that one of the following holds:
(i) $x$ is irrational, and $d$ is rational but not a positive integer; (ii) $x$ is rational but
not a natural number, and $d$ is irrational; (iii) there are natural numbers
$s_1, s_2, p_1, p_2, q_1, q_2$ with $p_1 > 0$, $p_2 > 0$,
$\gcd(p_1, q_1) = \gcd(p_2, q_2) = \gcd(q_1, q_2) = 1$ and $q_1 \ge 3$ such that
$x = s_1 + p_1/q_1$ and $d = s_2 + p_2/q_2$, and $d$ is not a natural number. Then
$I_n \cup J(x, m, d)$ is not an MSTD set. Here the natural numbers include $0$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 19
(`integers-2026-A58-lem-19`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_coprime_den (n m : ℕ) (x d : ℝ)
    (hn : 3 ≤ n) (hm : 2 ≤ m) (hx₀ : 0 < x)
    (hx₁ : x < (n : ℝ) - 1)
    (hcase : (Irrational x ∧ d ∈ Set.range ((↑) : ℚ → ℝ) ∧ ∀ k : ℕ, 0 < k → d ≠ k) ∨
      (x ∈ Set.range ((↑) : ℚ → ℝ) ∧ x ∉ Set.range ((↑) : ℕ → ℝ) ∧ Irrational d) ∨
      (∃ s₁ s₂ p₁ p₂ q₁ q₂ : ℕ, 0 < p₁ ∧ 0 < p₂ ∧ Nat.Coprime p₁ q₁ ∧ Nat.Coprime p₂ q₂ ∧
        Nat.Coprime q₁ q₂ ∧ 3 ≤ q₁ ∧ x = s₁ + (p₁ : ℝ) / q₁ ∧ d = s₂ + (p₂ : ℝ) / q₂ ∧
        d ∉ Set.range ((↑) : ℕ → ℝ))) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Uniqueness of integer points when the denominators share a factor.** Let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $p_1, p_2 > 0$, $\gcd(p_1, q_1) = 1$,
$\gcd(p_2, q_2) = 1$ and $\gcd(q_1, q_2) > 1$, and let $x = s_1 + p_1/q_1$ and
$d = s_2 + p_2/q_2$. For indices $i, i', j, j' \in \{1, \dots, q_2 - 1\}$: if $x + id$ and
$x + i'd$ are both nonnegative integers then $i = i'$; if $2x + jd$ and $2x + j'd$ are both
nonnegative integers then $j = j'$; and if $x + id$ and $2x + jd$ are both nonnegative integers
then $i \ne j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 20
(`integers-2026-A58-lem-20`). -/
public theorem_wanted add_mul_mem_nat_unique_of_one_lt_gcd (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hc₁ : Nat.Coprime p₁ q₁) (hc₂ : Nat.Coprime p₂ q₂) (hl : 1 < Nat.gcd q₁ q₂)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) :
    (∀ i i' : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ i' → i' ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → x + i' * d ∈ Set.range ((↑) : ℕ → ℝ) → i = i') ∧
    (∀ j j' : ℕ, 1 ≤ j → j ≤ q₂ - 1 → 1 ≤ j' → j' ≤ q₂ - 1 →
      2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j' * d ∈ Set.range ((↑) : ℕ → ℝ) → j = j') ∧
    (∀ i j : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ j → j ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → i ≠ j)

/-- **An interval and an overlapping progression whose denominators share a factor are not MSTD.**
Let $n \ge 3$ and $m \ge 2$ be natural numbers, and let $s_1, s_2, p_1, p_2, q_1, q_2$ be natural
numbers with $p_1 > 0$, $p_2 > 0$, $\gcd(p_1, q_1) = \gcd(p_2, q_2) = 1$ and $\gcd(q_1, q_2) > 1$.
Let $x = s_1 + p_1/q_1$ and $d = s_2 + p_2/q_2$, where a fraction with denominator $0$ is read as
$0$, and suppose that $x < n - 1 < d$. Write $I_n = \{0, 1, \dots, n - 1\}$ and
$J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$. Then $I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 21
(`integers-2026-A58-lem-21`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_of_one_lt_gcd (n m : ℕ) (x d : ℝ)
    (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hc₁ : Nat.Coprime p₁ q₁) (hc₂ : Nat.Coprime p₂ q₂)
    (hl : 1 < Nat.gcd q₁ q₂) (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂)
    (hx₁ : x < (n : ℝ) - 1) (hdn : (n : ℝ) - 1 < d) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **No integer points for a half-integer start and an odd denominator.** Let $s_1, s_2, p_2, q_2$
be natural numbers with $q_2$ odd, and let $x = s_1 + 1/2$ and $d = s_2 + p_2/q_2$. Then
$x + id$ is not a nonnegative integer for any natural number $i$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 22
(`integers-2026-A58-lem-22`). -/
public theorem_wanted add_mul_not_mem_nat_of_half (x d : ℝ) (s₁ s₂ p₂ q₂ : ℕ)
    (hq₂ : Nat.Coprime 2 q₂)
    (hx : x = s₁ + 1 / 2) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **Interval plus progression with half-integer start and odd-denominator step is not MSTD.**
Let $I_n = \{0, 1, \dots, n - 1\}$ and $J(x, m, d) = \{x + id : i = 0, 1, \dots, m\}$, as finite
sets of reals. Let $n \ge 3$, $m \ge 2$, $s_1$, $s_2$ and $p_2$ be natural numbers and $q_2$ an
odd natural number, and let $x = s_1 + 1/2$ and $d = s_2 + p_2/q_2$. If $x < n - 1 < d$, then
$I_n \cup J(x, m, d)$ is not an MSTD set.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 23
(`integers-2026-A58-lem-23`). -/
public theorem_wanted not_isMSTDSet_intervalAP_overlap_half_odd_den (n m : ℕ) (x d : ℝ)
    (s₁ s₂ p₂ q₂ : ℕ) (hn : 3 ≤ n) (hm : 2 ≤ m)
    (hq₂ : Nat.Coprime 2 q₂) (hx : x = s₁ + 1 / 2) (hd : d = s₂ + (p₂ : ℝ) / q₂)
    (hx₁ : x < (n : ℝ) - 1) (hdn : (n : ℝ) - 1 < d) :
    ¬ IsMSTDSet (realIntervalSet n ∪ realAPSet x m d)

/-- **Two overlapping progressions with rational ratios, outside two open cases, are not MSTD.**
For real numbers $x, d$ and a natural number $m$, write
$J(x, m, d) = \{x + id : i = 0, 1, \ldots, m\}$. Let $x_1, x_2, d_1, d_2$ be real numbers with
$d_1 > 0$, let $m_1, m_2$ be natural numbers with $x_2 < x_1 + m_1 d_1$, and let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $p_1, p_2, q_1, q_2 > 0$,
$\gcd(p_1, q_1) = \gcd(p_2, q_2) = 1$, $(x_2 - x_1)/d_1 = s_1 + p_1/q_1$ and
$d_2/d_1 = s_2 + p_2/q_2$. Suppose that neither of the following holds: (i) $\gcd(q_1, q_2) > 1$
and $0 < d_2 < (m_1 - 1) d_1$; (ii) $q_1 = 2$, $\gcd(2, q_2) = 1$ and $0 < d_2 < (m_1 - 1) d_1$.
Then $J(x_1, m_1, d_1) \cup J(x_2, m_2, d_2)$ is not an MSTD set.

Since $d_1 > 0$ and $d_2/d_1 = s_2 + p_2/q_2 > 0$, also $d_2 > 0$, so the condition
$x_2 < x_1 + m_1 d_1$ says that the smallest element of $J(x_2, m_2, d_2)$ is less than the largest
element of $J(x_1, m_1, d_1)$. Cases (i) and (ii) are the two cases the source leaves open.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Theorem 2
(`integers-2026-A58-thm-2`). -/
public theorem_wanted not_isMSTDSet_union_two_ap_overlap (x₁ x₂ d₁ d₂ : ℝ) (m₁ m₂ : ℕ)
    (hd₁ : 0 < d₁) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hq₁ : 0 < q₁)
    (hq₂ : 0 < q₂) (hcop₁ : Nat.Coprime p₁ q₁) (hcop₂ : Nat.Coprime p₂ q₂)
    (hx : (x₂ - x₁) / d₁ = s₁ + (p₁ : ℝ) / q₁) (hd : d₂ / d₁ = s₂ + (p₂ : ℝ) / q₂)
    (hlt : x₂ < x₁ + m₁ * d₁)
    (hexc₁ : ¬ (1 < Nat.gcd q₁ q₂ ∧ 0 < d₂ ∧ d₂ < ((m₁ : ℝ) - 1) * d₁))
    (hexc₂ : ¬ (q₁ = 2 ∧ Nat.Coprime 2 q₂ ∧ 0 < d₂ ∧ d₂ < ((m₁ : ℝ) - 1) * d₁)) :
    ¬ IsMSTDSet (realAPSet x₁ m₁ d₁ ∪ realAPSet x₂ m₂ d₂)

/-- **No nonnegative integer points for an irrational start and a rational difference.** Let
$x$ be an irrational real number and $d$ a rational number. Then for all natural numbers $i$ and
$j$, neither $x + id$ nor $2x + jd$ is a nonnegative integer.

The paper assumes $d \in \mathbb{Q} \setminus \mathbb{N}$; the claim holds for every rational $d$,
so that restriction is not stated.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_irrational_of_rat (x d : ℝ) (hx : Irrational x)
    (hd : d ∈ Set.range ((↑) : ℚ → ℝ)) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **Nonnegative integer points for a rational start and an irrational difference.** Let $x$ be
a rational number that is not a nonnegative integer, and let $d$ be an irrational real number.
Then $x + id$ is not a nonnegative integer for any natural number $i$, and $2x + jd$ is not a
nonnegative integer for any natural number $j \ge 1$.

As printed, the paper's Lemma 18 (ii) also claims $2x + 0 \cdot d \notin \mathbb{N}$, which fails
at $x = 1/2$ (where $2x = 1$); the paper's proof ("then $d \in \mathbb{Q}$") covers only $j \ge 1$,
and the condition that the denominator of $x$ be at least $3$ is attached only to part (iii).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_rat_of_irrational (x d : ℝ)
    (hx : x ∈ Set.range ((↑) : ℚ → ℝ)) (hxn : x ∉ Set.range ((↑) : ℕ → ℝ)) (hd : Irrational d)
    (i j : ℕ) (hj : 1 ≤ j) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

/-- **No integer points for coprime denominators, the first at least 3.** Let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $\gcd(p_1, q_1) = 1$, $\gcd(q_1, q_2) = 1$
and $q_1 \ge 3$, and let $x = s_1 + p_1/q_1$ and $d = s_2 + p_2/q_2$. Then for all natural numbers
$i$ and $j$, neither $x + id$ nor $2x + jd$ is a nonnegative integer.

The paper's further hypotheses ($p_1, p_2, q_2 > 0$, $\gcd(p_2, q_2) = 1$, $d \notin \mathbb{N}$)
are not needed and are not stated ($p_1 > 0$ and $q_2 > 0$ already follow from the two coprimality
conditions and $q_1 \ge 3$).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem_wanted add_mul_not_mem_nat_of_coprime_den (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hc₁ : Nat.Coprime p₁ q₁) (hq : Nat.Coprime q₁ q₂) (hq₁ : 3 ≤ q₁)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ)

end

end MetaMathlibExt
