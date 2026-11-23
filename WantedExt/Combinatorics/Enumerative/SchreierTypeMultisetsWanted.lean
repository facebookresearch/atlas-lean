/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear recurrences from counting Schreier-type multisets

Statements from Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and
Zachary Louis Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26
(2026), Article A53.

The paper's `ℕ` is the positive integers. For positive `s, p, n`:

* `A^{(s)}_{p,n}` is the set of multisets `F` drawn from `{1^s, …, (n - 1)^s, n}` (each of
  `1, …, n - 1` with multiplicity at most `s`, and `n` at most once) with `n ∈ F` and
  `min F ≥ p|F|` (`schreierMultisetCount`);
* `B^{(s)}_{p,n}` is the colored version: the `s` copies of each `k < n` carry distinct colors
  `0, …, s - 1`, encoded as pairs `(k, c)`, and `n` is the single pair `(n, 0)`
  (`coloredSchreierMultisetCount`);
* `D_{u,n}` is the set of Schreier sets `F ⊆ G_{u,n}` containing `⌊(un - 1)/(u - 1)⌋`, where
  `G_{u,n}` is the set of the first `n` positive integers not divisible by `u`
  (`schreierAvoidingMultiplesCount`), with `IsSchreier` from
  `WantedExt/Combinatorics/Enumerative/SchreierTypeSetsWanted.lean`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Fib.Basic
public import WantedExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

@[expose] public section

/-- **Ground multiset for Schreier-type multisets.** For natural numbers $s$ and $n$, this is the
multiset $\{1^s, \dots, (n - 1)^s, n\}$, in which each of $1, \dots, n - 1$ has multiplicity $s$
and $n$ appears once.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `A^{(s)}_{p,n}`). -/
def schreierMultisetPool (s n : ℕ) : Multiset ℕ :=
  (∑ k ∈ Finset.Icc 1 (n - 1), Multiset.replicate s k) + {n}

/-- **Number of Schreier-type multisets.** For natural numbers $s$, $p$ and $n$, $|A^{(s)}_{p,n}|$
is the number of distinct sub-multisets $F$ of $\{1^s, \dots, (n - 1)^s, n\}$ (each of
$1, \dots, n - 1$ with multiplicity $s$, and $n$ once) such that $n \in F$ and every element of $F$
is at least $p|F|$, where $|F|$ counts multiplicity.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `A^{(s)}_{p,n}`). -/
def schreierMultisetCount (s p n : ℕ) : ℕ :=
  ((schreierMultisetPool s n).powerset.toFinset.filter fun F =>
    n ∈ F ∧ ∀ x ∈ F, p * Multiset.card F ≤ x).card

/-- **Small values of the Schreier multiset count.** Let $|A^{(s)}_{p,n}|$ be the number of
distinct sub-multisets $F$ of $\{1^s, \dots, (n - 1)^s, n\}$ with $n \in F$ and every element of
$F$ at least $p|F|$, where $|F|$ counts multiplicity. Then $|A^{(2)}_{1,4}| = 4$ and
$|A^{(2)}_{2,5}| = 2$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 1. -/
theorem schreierMultisetCount_small :
    schreierMultisetCount 2 1 4 = 4 ∧ schreierMultisetCount 2 2 5 = 2 := by
  decide +kernel

/-- **Counting colored Schreier-type multisets.** For natural numbers $s$, $p$ and $n$, give each
of $1, \dots, n - 1$ the $s$ colors $0, \dots, s - 1$, writing $k_c$ for $k$ with color $c$, and
let $n$ appear once, uncolored. Then $|B^{(s)}_{p,n}|$ is the number of sets $F$ of colored
integers drawn from $\{1_0, \dots, 1_{s-1}, \dots, (n-1)_0, \dots, (n-1)_{s-1}, n\}$ that
contain $n$ and satisfy $\min F \ge p|F|$, where the minimum is taken over the underlying
integers.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `B^{(s)}_{p,n}`). -/
def coloredSchreierMultisetCount (s p n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1) ×ˢ Finset.range s ∪ {(n, 0)}).powerset.filter fun F =>
    (n, 0) ∈ F ∧ ∀ x ∈ F, p * F.card ≤ x.1).card

/-- **Small values of the colored Schreier multiset count.** The numbers of colored Schreier-type
multisets satisfy $|B^{(2)}_{1,4}| = 6$ and $|B^{(2)}_{2,5}| = 3$ (Table 2 of the paper).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 2. -/
theorem coloredSchreierMultisetCount_small :
    coloredSchreierMultisetCount 2 1 4 = 6 ∧ coloredSchreierMultisetCount 2 2 5 = 3 := by
  decide

/-- **First non-multiples of an integer.** For natural numbers $u$ and $n$, $G_{u,n}$ is the set of
positive integers $k \le un$ with $u \nmid k$ such that at most $n$ of the integers in $[1, k]$
are not divisible by $u$. For $u \ge 1$ the bound $k \le un$ is automatic, and $G_{u,n}$ is the
set of the first $n$ positive integers not divisible by $u$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `G_{u,n}`). -/
def firstNonMultiples (u n : ℕ) : Finset ℕ :=
  (Finset.range (u * n + 1)).filter fun k =>
    0 < k ∧ ¬ u ∣ k ∧ ((Finset.Icc 1 k).filter fun j => ¬ u ∣ j).card ≤ n

/-- **The first four positive integers not divisible by 3.** The set $G_{3,4}$ of the first four
positive integers not divisible by $3$ is $\{1, 2, 4, 5\}$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1. -/
theorem firstNonMultiples_three_four : firstNonMultiples 3 4 = {1, 2, 4, 5} := by
  decide

/-- **Schreier sets avoiding multiples.** For natural numbers $u$ and $n$, let $G_{u,n}$ be the
set of the first $n$ positive integers not divisible by $u$ (taken to be empty when $u = 0$), and
call a finite set $F$ of natural numbers Schreier when every element of $F$ is at least $|F|$.
Then $|D_{u,n}|$ is the number of Schreier sets $F \subseteq G_{u,n}$ with
$\lfloor (un - 1)/(u - 1) \rfloor \in F$.

For $u \le 1$ or $n = 0$ the set $G_{u,n}$ is empty and the count is $0$; otherwise $un - 1$ and
$u - 1$ are positive, so the natural-number subtraction and floor division agree with the real
expression.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 1 (definition of `D_{u,n}`). -/
def schreierAvoidingMultiplesCount (u n : ℕ) : ℕ :=
  ((firstNonMultiples u n).powerset.filter fun F =>
    (u * n - 1) / (u - 1) ∈ F ∧ IsSchreier F).card

/-- **Small values of the count of Schreier sets avoiding multiples.** The numbers of Schreier-type
sets avoiding multiples satisfy $|D_{2,6}| = 12$ and $|D_{3,6}| = 9$ (Table 3 of the paper).

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Table 3. -/
theorem schreierAvoidingMultiplesCount_small :
    schreierAvoidingMultiplesCount 2 6 = 12 ∧ schreierAvoidingMultiplesCount 3 6 = 9 := by
  decide

/-- **Parent sequence b for Schreier-type multisets.** For natural numbers $s$ and $p$, the
sequence $b^{(s)}_{p,n}$, $n \ge 0$, is defined by $b^{(s)}_{p,n} = 0$ for $n \le (p - 1)s$,
$b^{(s)}_{p,n} = 1$ for $(p - 1)s < n \le ps + 1$, and
$b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for $n \ge ps + 2$, where $p - 1$ is read
as $0$ when $p = 0$.

The paper indexes from $n = 1$; here $b^{(s)}_{p,0} = 0$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3 (definition of `b^{(s)}_{p,n}`). -/
def schreierParentB (s p : ℕ) (n : ℕ) : ℕ :=
  if n ≤ (p - 1) * s then 0
  else if _h : n ≤ p * s + 1 then 1
  else schreierParentB s p (n - 1) + schreierParentB s p (n - 1 - p * s)
decreasing_by all_goals omega

/-- **The parent sequence b vanishes for small indices.** For natural numbers $s$ and $p$, let
$b^{(s)}_{p,n}$ be the parent sequence: $0$ for $n \le (p - 1)s$, $1$ for
$(p - 1)s < n \le ps + 1$, and $b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for
$n \ge ps + 2$, where $p - 1$ is read as $0$ when $p = 0$. Then $b^{(s)}_{p,n} = 0$
for every natural number $n$ with $n \le (p - 1)s$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_of_le {s p n : ℕ} (hn : n ≤ (p - 1) * s) : schreierParentB s p n = 0 := by
  rw [schreierParentB]
  simp [hn]

/-- **The parent sequence b equals one on its initial window.** For natural numbers $s$ and $p$,
let $b^{(s)}_{p,n}$ be the parent sequence: $0$ for $n \le (p - 1)s$, $1$ for
$(p - 1)s < n \le ps + 1$, and $b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for
$n \ge ps + 2$, where $p - 1$ is read as $0$ when $p = 0$. Then $b^{(s)}_{p,n} = 1$ for every
natural number $n$ with $(p - 1)s < n \le ps + 1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_of_mem {s p n : ℕ} (h₁ : (p - 1) * s < n) (h₂ : n ≤ p * s + 1) :
    schreierParentB s p n = 1 := by
  rw [schreierParentB]
  split_ifs <;> first | rfl | omega

/-- **Recurrence for the parent sequence b.** For natural numbers $s$ and $p$, let
$b^{(s)}_{p,n}$ be the parent sequence: $0$ for $n \le (p - 1)s$, $1$ for
$(p - 1)s < n \le ps + 1$, and $b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for
$n \ge ps + 2$, where $p - 1$ is read as $0$ when $p = 0$. Then
$b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for every natural number $n \ge ps + 2$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 3. -/
theorem schreierParentB_rec {s p n : ℕ} (hn : p * s + 2 ≤ n) :
    schreierParentB s p n = schreierParentB s p (n - 1) + schreierParentB s p (n - 1 - p * s) := by
  have : (p - 1) * s ≤ p * s := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [schreierParentB]
  split_ifs <;> first | rfl | omega

/-- **The parent sequence $d_{u,n}$.** For natural numbers $u$ and $n$, define $d_{u,n}$ by
recursion on $n$: $d_{u,n} = 1$ if $n < 2u$ or $u = 0$, and otherwise
$d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}$.

The paper takes $u \ge 2$ and indexes from $n = 1$, with $d_{u,n} = 1$ for $1 \le n \le 2u - 1$;
here $d_{u,0} = 1$ as well, and the degenerate case $u = 0$ is set to $1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4 (definition of `d_{u,n}`). -/
def schreierParentD (u : ℕ) (n : ℕ) : ℕ :=
  if _h : n < 2 * u ∨ u = 0 then 1
  else schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1)
decreasing_by all_goals omega

/-- **Initial values of the parent sequence.** For all natural numbers $u$ and $n$ with $n < 2u$,
the parent sequence $d_{u,n}$ satisfies $d_{u,n} = 1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4. -/
theorem schreierParentD_of_lt {u n : ℕ} (hn : n < 2 * u) : schreierParentD u n = 1 := by
  rw [schreierParentD]
  split_ifs <;> first | rfl | omega

/-- **Recurrence for the parent sequence.** For all natural numbers $u \ge 1$ and $n \ge 2u$, the
parent sequence $d_{u,n}$ satisfies $d_{u,n} = d_{u,n-u} + d_{u,n-2u+1}$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Section 4. -/
theorem schreierParentD_rec {u n : ℕ} (hu : 1 ≤ u) (hn : 2 * u ≤ n) :
    schreierParentD u n = schreierParentD u (n - u) + schreierParentD u (n - 2 * u + 1) := by
  rw [schreierParentD]
  split_ifs <;> first | rfl | omega

/-- **Formula and recurrence for Schreier-type multisets.** Let $s, p \ge 1$, and for $n \ge 1$
let $|A^{(s)}_{p,n}|$ be the number of distinct sub-multisets $F$ of
$\{1^s, \dots, (n - 1)^s, n\}$ with $n \in F$ and $\min F \ge p|F|$, where $|F|$ counts
multiplicity. For $1 \le n \le sp + 1$,

$$|A^{(s)}_{p,n}| = \sum_{k=1}^{\lfloor (sn+1)/(sp+1) \rfloor} \binom{n - pk + k - 2}{k - 1},$$

and for $n \ge sp + 2$,

$$|A^{(s)}_{p,n}| = \sum_{i=0}^{s} |A^{(s)}_{p,n-1-ip}|.$$

In the first sum $pk \le n$, so the top $n - pk + k - 2$ is negative only for $k = 1$ and $n = p$,
where the coefficient is $\binom{-1}{0} = 1$; the natural-number subtraction gives
$\binom{0}{0} = 1$ there as well.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 1 (`integers-2026-A53-thm-1`). -/
public theorem_wanted schreierMultisetCount_formula_and_recurrence {s p : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) :
    (∀ n, 1 ≤ n → n ≤ s * p + 1 →
      schreierMultisetCount s p n =
        ∑ k ∈ Finset.Icc 1 ((s * n + 1) / (s * p + 1)), (n - p * k + k - 2).choose (k - 1)) ∧
    ∀ n, s * p + 2 ≤ n →
      schreierMultisetCount s p n = ∑ i ∈ Finset.range (s + 1), schreierMultisetCount s p (n - 1 - i * p)

/-- **Closed form and recurrence for colored Schreier multiset counts.** Let $s \ge 1$ and
$p \ge 1$, and write $|B^{(s)}_{p,n}|$ for the number of colored Schreier-type multisets. For
$1 \le n \le sp + 1$,
$$|B^{(s)}_{p,n}| = \sum_{k=1}^{\lfloor (ns+1)/(ps+1) \rfloor} \binom{(n - kp)s}{k - 1},$$
and for $n \ge sp + 2$,
$$|B^{(s)}_{p,n}| = \sum_{i=0}^{s} \binom{s}{i} \, |B^{(s)}_{p,n-1-ip}|.$$

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 2 (`integers-2026-A53-thm-2`). -/
public theorem_wanted coloredSchreierMultisetCount_formula_and_recurrence {s p : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) :
    (∀ n, 1 ≤ n → n ≤ s * p + 1 →
      coloredSchreierMultisetCount s p n =
        ∑ k ∈ Finset.Icc 1 ((n * s + 1) / (p * s + 1)), ((n - k * p) * s).choose (k - 1)) ∧
    ∀ n, s * p + 2 ≤ n →
      coloredSchreierMultisetCount s p n =
        ∑ i ∈ Finset.range (s + 1), s.choose i * coloredSchreierMultisetCount s p (n - 1 - i * p)

/-- **Binomial-sum formula for the parent sequence b.** Let $b^{(s)}_{p,n}$ be the parent
sequence: $0$ for $n \le (p - 1)s$, $1$ for $(p - 1)s < n \le ps + 1$, and
$b^{(s)}_{p,n} = b^{(s)}_{p,n-1} + b^{(s)}_{p,n-1-ps}$ for $n \ge ps + 2$. For positive integers
$s$, $p$ and $n$,

$$b^{(s)}_{p,n} = \sum_{i=0}^{\lfloor (n - s(p-1) - 1)/(sp+1) \rfloor}
\binom{n - s(p-1) - 1 - spi}{i},$$

where the sum is empty when $n \le s(p - 1)$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 1 (`integers-2026-A53-prop-1`). -/
public theorem_wanted schreierParentB_eq_sum_choose {s p n : ℕ} (hs : 1 ≤ s) (hp : 1 ≤ p)
    (hn : 1 ≤ n) :
    schreierParentB s p n =
      ∑ i ∈ (Finset.range n).filter (fun i => (s * p + 1) * i + s * (p - 1) + 1 ≤ n),
        (n - s * (p - 1) - 1 - s * p * i).choose i

/-- **Colored Schreier multiset counts are a subsequence of the parent sequence.** For all
positive integers $s$, $p$ and $n$, the number $|B^{(s)}_{p,n}|$ of colored Schreier-type
multisets equals the term $b^{(s)}_{p,ns-s+1}$ of the parent sequence $b^{(s)}_{p,m}$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Lemma 1 (`integers-2026-A53-lem-1`). -/
public theorem_wanted coloredSchreierMultisetCount_eq_schreierParentB {s p n : ℕ} (hs : 1 ≤ s)
    (hp : 1 ≤ p) (hn : 1 ≤ n) :
    coloredSchreierMultisetCount s p n = schreierParentB s p (n * s - s + 1)

/-- **The non-multiples of an integer as values of a floor function.** For every integer $u \ge 2$,
the set $\{\lfloor (un - 1)/(u - 1) \rfloor : n \ge 1\}$, with $n$ ranging over the positive
integers, is the set of positive integers not divisible by $u$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Lemma 2 (`integers-2026-A53-lem-2`). -/
public theorem_wanted image_floor_eq_nonMultiples {u : ℕ} (hu : 2 ≤ u) :
    (fun n => (u * n - 1) / (u - 1)) '' {n | 1 ≤ n} = {m | 1 ≤ m ∧ ¬ u ∣ m}

/-- **Binomial sum formula for the parent sequence.** For all natural numbers $u \ge 2$ and
$n \ge 1$, the parent sequence $d_{u,n}$ satisfies
$$
d_{u,n} = \sum_{i=0}^{\lfloor (n-1)/u \rfloor} \binom{\lfloor (n + (u-1)i - u)/(2u-1) \rfloor}{i}.
$$

The numerator $n + (u-1)i - u$ is negative only when $i = 0$ and $n < u$. There it is read as
$0$ (truncated subtraction), so the term is $\binom{0}{0} = 1$, which agrees with the paper's
$\binom{-1}{0} = 1$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 2 (`integers-2026-A53-prop-2`). -/
public theorem_wanted schreierParentD_eq_sum_choose {u n : ℕ} (hu : 2 ≤ u) (hn : 1 ≤ n) :
    schreierParentD u n =
      ∑ i ∈ Finset.range ((n - 1) / u + 1), ((n + (u - 1) * i - u) / (2 * u - 1)).choose i

/-- **Schreier sets avoiding multiples are counted by a subsequence of the parent sequence.**
For every integer $u \ge 2$ and every integer $n \ge 1$, the number $|D_{u,n}|$ of Schreier-type
sets avoiding multiples of $u$ equals the term $d_{u,un-(u-1)}$ of the parent sequence $d_{u,m}$.

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Proposition 3 (`integers-2026-A53-prop-3`). -/
public theorem_wanted schreierAvoidingMultiplesCount_eq_schreierParentD {u n : ℕ} (hu : 2 ≤ u)
    (hn : 1 ≤ n) :
    schreierAvoidingMultiplesCount u n = schreierParentD u (u * n - (u - 1))

/-- **Fibonacci values and a recurrence for Schreier sets avoiding multiples.** Let $u \ge 2$,
write $|D_{u,n}|$ for the number of Schreier-type sets avoiding multiples of $u$, and write $F_n$
for the Fibonacci numbers, with $F_0 = 0$ and $F_1 = 1$. For $1 \le n \le 2u - 1$,
$|D_{u,n}| = F_n$, and for $n \ge 2u$, as an identity of integers,
$$|D_{u,n}| = \sum_{i=1}^{u} (-1)^{i-1} \binom{u}{i} |D_{u,n-i}| + |D_{u,n-2u+1}|.$$

Source: Hùng Việt Chu, Yubo Geng, Julian King, Steven J. Miller, Garrett Tresch and Zachary Louis
Vasseur, *Linear Recurrences from Counting Schreier-Type Multisets*, INTEGERS 26 (2026),
Article A53, Theorem 3 (`integers-2026-A53-thm-3`). -/
public theorem_wanted schreierAvoidingMultiplesCount_fib_and_recurrence {u : ℕ} (hu : 2 ≤ u) :
    (∀ n, 1 ≤ n → n ≤ 2 * u - 1 → schreierAvoidingMultiplesCount u n = Nat.fib n) ∧
    ∀ n, 2 * u ≤ n →
      (schreierAvoidingMultiplesCount u n : ℤ) =
        ∑ i ∈ Finset.Icc 1 u,
            (-1 : ℤ) ^ (i - 1) * u.choose i * schreierAvoidingMultiplesCount u (n - i) +
          schreierAvoidingMultiplesCount u (n - 2 * u + 1)

end

end MetaMathlibExt
