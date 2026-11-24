/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Sets with more products than quotients

This module defines MPTQ sets and describes which pairings of four distinct positive
real numbers can have equal products.
-/

@[expose] public section

namespace MetaMathlibExt

open Pointwise

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

/-- **Adjoining an element that adds no more products than quotients.** Let $A$ be a finite set
of real numbers that is not an MPTQ set, let $x$ be a real number, let $n \le m$ be natural
numbers, and write $A' = A \cup \{x\}$. If $|A' \cdot A'| \le |A \cdot A| + n$ and
$|A/A| + m \le |A'/A'|$, where $X \cdot X$ and $X/X$ denote the product set and quotient set of
$X$, then $A'$ is not an MPTQ set.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 1 (`integers-2024-A96-lem-1`). -/
public theorem not_isMPTQSet_insert_of_le {A : Finset ℝ} {x : ℝ} {n m : ℕ}
    (hA : ¬ IsMPTQSet A) (hn : (insert x A * insert x A).card ≤ (A * A).card + n)
    (hm : (A / A).card + m ≤ (insert x A / insert x A).card) (hnm : n ≤ m) :
    ¬ IsMPTQSet (insert x A) := by
  intro h
  have hz : (0 : ℝ) ∉ A := fun hzero => h.1 (Finset.mem_insert_of_mem hzero)
  have hle : (A * A).card ≤ (A / A).card :=
    le_of_not_gt (fun hlt => hA ⟨hz, hlt⟩)
  refine (not_lt_of_ge ?_) h.2
  calc
    (insert x A * insert x A).card ≤ (A * A).card + n := hn
    _ ≤ (A / A).card + m := Nat.add_le_add hle hnm
    _ ≤ (insert x A / insert x A).card := hm

set_option linter.unusedVariables false in
/-- **One equal pairing of products excludes the other two.** Let $a$, $b$, $c$, $d$ be pairwise
distinct positive real numbers with $ab = cd$. Then $ad \neq bc$ and $ac \neq bd$.

Source: Anupriya Shetty and B. R. Shankar, *On The Minimum Cardinality of MPTQ Sets*,
INTEGERS 24 (2024), Article A96, Lemma 2 (`integers-2024-A96-lem-2`). -/
theorem mul_ne_of_mul_eq_of_distinct {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : a * b = c * d) : a * d ≠ b * c ∧ a * c ≠ b * d := by
  constructor
  · intro hadbc
    apply hac
    apply mul_right_cancel₀ (add_pos hb hd).ne'
    rw [mul_add, mul_add, h, hadbc]
    ac_rfl
  · intro hacbd
    apply had
    apply mul_right_cancel₀ (add_pos hb hc).ne'
    rw [mul_add, mul_add, h, hacbd]
    ac_rfl

end MetaMathlibExt
