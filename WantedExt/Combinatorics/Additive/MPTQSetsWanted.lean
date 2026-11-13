/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import WantedExt.Combinatorics.Additive.UnionTwoAPNotMSTDWanted

/-!
# The minimum cardinality of MPTQ sets

Statements from Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96.

For a finite set `A ⊆ ℝ ∖ {0}`, `A.A = {a a'}` and `A/A = {a / a'}`; `A` is an MPTQ (more
products than quotients) set when `|A.A| > |A/A|`. Integer sets are viewed as sets of reals.
MSTD sets reuse `IsMSTDSet`.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- **MPTQ set.** A finite set $A$ of real numbers is an MPTQ (more products than quotients) set
when $0 \notin A$ and $|A/A| < |A \cdot A|$, where $A \cdot A = \{ab : a, b \in A\}$ is the
product set, $A/A = \{a/b : a, b \in A\}$ is the quotient set, and $|X|$ is the number of
elements of $X$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
def IsMPTQSet (A : Finset ℝ) : Prop :=
  (0 : ℝ) ∉ A ∧ (A / A).card < (A * A).card

/-- **A singleton is not an MPTQ set.** For every real number $a$, the one-element set $\{a\}$
is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_singleton (a : ℝ) : ¬ IsMPTQSet {a} := by
  simp [IsMPTQSet]

/-- **Sets containing zero are not MPTQ sets.** If $A$ is a finite set of real numbers with
$0 \in A$, then $A$ is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Definition 1. -/
theorem not_isMPTQSet_of_zero_mem {A : Finset ℝ} (h : (0 : ℝ) ∈ A) : ¬ IsMPTQSet A :=
  fun hA => hA.1 h

/-- **Hegarty: no seven-element MSTD set of integers.** No set of seven integers, viewed as a set
of real numbers, is an MSTD set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted not_isMSTDSet_int_of_card_eq_seven (A : Finset ℤ) (hA : A.card = 7) :
    ¬ IsMSTDSet (A.image ((↑) : ℤ → ℝ))

/-- **Hegarty's classification of MSTD sets of size eight.** Let $A$ be a set of eight integers,
regarded as a set of real numbers, and let $S = \{0, 2, 3, 4, 7, 11, 12, 14\}$. Then $A$ is an
MSTD set if and only if $A = \{as + b : s \in S\}$ for some integers $a \neq 0$ and $b$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 1 (`integers-2024-A96-thm-1`). -/
public theorem_wanted isMSTDSet_int_of_card_eq_eight_iff (A : Finset ℤ) (hA : A.card = 8) :
    IsMSTDSet (A.image ((↑) : ℤ → ℝ)) ↔
      ∃ a b : ℤ, a ≠ 0 ∧ A = ({0, 2, 3, 4, 7, 11, 12, 14} : Finset ℤ).image (fun s => a * s + b)

/-- **Chu's bound for MPTQ sets of positive reals.** Every MPTQ set whose elements are all
positive real numbers has at least $8$ elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted eight_le_card_of_isMPTQSet_of_pos {A : Finset ℝ} (hA : IsMPTQSet A)
    (hpos : ∀ a ∈ A, 0 < a) : 8 ≤ A.card

/-- **Chu's bound for MPTQ sets with a negative element.** Every MPTQ set of real numbers that
contains a negative number has at least $5$ elements.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 2 (`integers-2024-A96-thm-2`). -/
public theorem_wanted five_le_card_of_isMPTQSet_of_neg {A : Finset ℝ} (hA : IsMPTQSet A)
    (hneg : ∃ a ∈ A, a < 0) : 5 ≤ A.card

/-- **Adjoining an element that adds no more products than quotients.** Let $A$ be a finite set
of real numbers that is not an MPTQ set, let $x$ be a real number, let $n \le m$ be natural
numbers, and write $A' = A \cup \{x\}$. If $|A' \cdot A'| \le |A \cdot A| + n$ and
$|A/A| + m \le |A'/A'|$, where $X \cdot X$ and $X/X$ denote the product set and quotient set of
$X$, then $A'$ is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 1 (`integers-2024-A96-lem-1`). -/
public theorem_wanted not_isMPTQSet_insert_of_le {A : Finset ℝ} {x : ℝ} {n m : ℕ}
    (hA : ¬ IsMPTQSet A) (hn : (insert x A * insert x A).card ≤ (A * A).card + n)
    (hm : (A / A).card + m ≤ (insert x A / insert x A).card) (hnm : n ≤ m) :
    ¬ IsMPTQSet (insert x A)

/-- **One equal pairing of products excludes the other two.** Let $a$, $b$, $c$, $d$ be pairwise
distinct positive real numbers with $ab = cd$. Then $ad \neq bc$ and $ac \neq bd$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 2 (`integers-2024-A96-lem-2`). -/
public theorem_wanted mul_ne_of_mul_eq_of_distinct {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : a * b = c * d) : a * d ≠ b * c ∧ a * c ≠ b * d

/-- **At most one square is the product of the other two.** Let $a$, $b$, $c$ be pairwise
distinct positive real numbers. Then at most one of the equations $a^2 = bc$, $b^2 = ac$ and
$c^2 = ab$ holds; that is, no two of them hold simultaneously.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 3 (`integers-2024-A96-lem-3`). -/
public theorem_wanted at_most_one_sq_eq_mul_of_distinct {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ (a ^ 2 = b * c ∧ b ^ 2 = a * c) ∧ ¬ (a ^ 2 = b * c ∧ c ^ 2 = a * b) ∧
      ¬ (b ^ 2 = a * c ∧ c ^ 2 = a * b)

/-- **Five-element sets with one negative element are not MPTQ sets.** If $A$ is a set of five
real numbers exactly one of which is negative, then $A$ is not an MPTQ set.

The source assumes the elements are nonzero; this is not needed, since a set containing $0$ is
never an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 4 (`integers-2024-A96-lem-4`). -/
public theorem_wanted not_isMPTQSet_of_card_five_one_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 1) : ¬ IsMPTQSet A

/-- **Five-element sets with two negative elements are not MPTQ sets.** If $A$ is a set of five
real numbers exactly two of which are negative, then $A$ is not an MPTQ set.

The source assumes the elements are nonzero; this is not needed, since a set containing $0$ is
never an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 5 (`integers-2024-A96-lem-5`). -/
public theorem_wanted not_isMPTQSet_of_card_five_two_neg {A : Finset ℝ} (hcard : A.card = 5)
    (hneg : (A.filter (· < 0)).card = 2) : ¬ IsMPTQSet A

/-- **Adjoining negatives preserves the MPTQ property.** Let $A$ be a finite set of positive real
numbers and $-A = \{-a : a \in A\}$. Then $A \cup (-A)$ is an MPTQ set if and only if $A$ is an
MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Proposition 1 (`integers-2024-A96-prop-1`). -/
public theorem_wanted isMPTQSet_union_neg_iff {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) :
    IsMPTQSet (A ∪ -A) ↔ IsMPTQSet A

/-- **No MPTQ set has five elements.** No set of five real numbers is an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 3 (`integers-2024-A96-thm-3`). -/
public theorem_wanted not_isMPTQSet_of_card_eq_five {A : Finset ℝ} (hcard : A.card = 5) :
    ¬ IsMPTQSet A

/-- **Adjoining multiples by a coprime prime preserves the MPTQ property.** Let $A$ be a finite
set of integers and $p$ a prime number such that every element of $A$ is coprime to $p$, and let
$pA = \{pa : a \in A\}$. Regarding sets of integers as sets of real numbers, $A \cup pA$ is an
MPTQ set if and only if $A$ is an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Theorem 4 (`integers-2024-A96-thm-4`). -/
public theorem_wanted isMPTQSet_union_prime_mul_iff (A : Finset ℤ) {p : ℕ} (hp : p.Prime)
    (hcop : ∀ a ∈ A, IsCoprime a (p : ℤ)) :
    IsMPTQSet ((A ∪ A.image ((p : ℤ) * ·)).image ((↑) : ℤ → ℝ)) ↔
      IsMPTQSet (A.image ((↑) : ℤ → ℝ))

end

end MetaMathlibExt
