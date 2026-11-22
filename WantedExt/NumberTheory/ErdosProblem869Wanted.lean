/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Disjoint

@[expose] public section

/-!
# Erdős Problem #869

If `A₁` and `A₂` are disjoint additive bases of order `2`, must their
union contain a minimal additive basis of order `2`?
-/

namespace MathlibExt.NumberTheory.ErdosProblem869Wanted

/-- **Sumset of a set of naturals.** For a set $A$ of natural numbers, $A + A$ is the set of
natural numbers $n$ such that $n = a + b$ for some $a, b \in A$. -/
def addSumset (A : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ A, a + b = n }

/-- **Additive basis of order 2.** A set $A$ of natural numbers is an additive basis of order $2$
if there is a natural number $N$ such that every natural number $n \ge N$ can be written as
$n = a + b$ with $a, b \in A$. -/
def IsAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ a ∈ A, ∃ b ∈ A, a + b = n

/-- **Minimal additive basis of order 2.** A set $A$ of natural numbers is a minimal additive
basis of order $2$ if it is an additive basis of order $2$ and, for every $a \in A$, infinitely
many natural numbers do not lie in the sumset $(A \setminus \{a\}) + (A \setminus \{a\})$. -/
def IsMinimalAdditiveBasisOrder2 (A : Set ℕ) : Prop :=
  IsAdditiveBasisOrder2 A ∧ ∀ a ∈ A, ((addSumset (A \ {a}))ᶜ).Infinite

/-- **Erdős Problem 869 (disjoint bases and minimal bases).** The statement that for all disjoint
sets $A_1$ and $A_2$ of natural numbers that are both additive bases of order $2$, there is a set
$B \subseteq A_1 \cup A_2$ that is a minimal additive basis of order $2$. -/
def Statement : Prop :=
  ∀ A1 A2 : Set ℕ, Disjoint A1 A2 → IsAdditiveBasisOrder2 A1 →
    IsAdditiveBasisOrder2 A2 →
    ∃ B : Set ℕ, B ⊆ A1 ∪ A2 ∧ IsMinimalAdditiveBasisOrder2 B

/-- **Erdős Problem 869 is false (Larsen).** There are disjoint sets $A_1$ and $A_2$ of natural
numbers, both additive bases of order $2$, such that no subset of $A_1 \cup A_2$ is a minimal
additive basis of order $2$.

Source: Daniel Larsen, Three questions of Erdős–Nathanson
on asymptotic bases of order 2, arXiv:2603.03472 (2026), https://arxiv.org/abs/2603.03472; Lean
proof of the negative answer to Erdős Problem 869, pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos869.lean#L3490.
Moved from `OpenConjectures/NumberTheory/ErdosProblem869`.
-/
public theorem_wanted Statement_refuted : ¬ Statement

end MathlibExt.NumberTheory.ErdosProblem869Wanted
