/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Erdős Problem 152: for any `M ≥ 1`, every sufficiently large finite Sidon set
`A ⊆ ℕ` has at least `M` sums `a ∈ A + A` isolated from the rest of the
sumset, i.e. with `a + 1 ∉ A + A` and `a - 1 ∉ A + A`.

Formalization note: since sums are naturals, `a - 1` uses truncated
subtraction and the predecessor condition is stated as `a = 0 ∨ a - 1 ∉ S`,
which is vacuously true at `a = 0` (where `0` has no predecessor in `ℕ`)
and is the true predecessor condition for `a ≥ 1`. This also keeps the
isolated-sum predicate decidable (an unbounded `∀ p : ℕ` predecessor
quantifier would not be).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted

/-! Source record `EP-152`. -/

/-- **Finite Sidon sets of natural numbers.** A finite set $A$ of natural numbers is a Sidon set
when every equality $a + b = c + d$ with $a, b, c, d \in A$ is trivial, that is, $a = c$ and
$b = d$, or $a = d$ and $b = c$. -/
def IsSidon (A : Finset ℕ) : Prop :=
  Set.IsSidon (A : Set ℕ)

/-- **Sumset of a finite set of natural numbers.** For a finite set $A$ of natural numbers, the
sumset $A + A$ is the finite set of all sums $x + y$ with $x, y \in A$. -/
def Sumset (A : Finset ℕ) : Finset ℕ :=
  (A.product A).image (fun p => p.1 + p.2)

/-- **Isolated elements of a set of natural numbers.** Let $S$ be a finite set of natural numbers.
A natural number $a$ is isolated in $S$ when $a \in S$, $a + 1 \notin S$, and either $a = 0$ or
$a - 1 \notin S$.

For $a = 0$ the condition on the predecessor is vacuous, since $0$ has no predecessor among the
natural numbers. -/
def IsIsolated (S : Finset ℕ) (a : ℕ) : Prop :=
  a ∈ S ∧ a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S)

/-- **Number of isolated elements.** For a finite set $S$ of natural numbers, the isolated count
of $S$ is the number of elements $a \in S$ with $a + 1 \notin S$ and either $a = 0$ or
$a - 1 \notin S$. -/
def IsolatedCount (S : Finset ℕ) : ℕ :=
  (S.filter (fun a => a + 1 ∉ S ∧ (a = 0 ∨ a - 1 ∉ S))).card

/-- **Erdős Problem 152 on isolated sums of Sidon sets.** A finite set $A$ of natural numbers is
a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$, and its
sumset is $A + A = \{x + y : x, y \in A\}$. An element $s$ of a finite set $S$ of natural numbers
is isolated in $S$ when $s + 1 \notin S$ and either $s = 0$ or $s - 1 \notin S$. The proposition
asserts that for every natural number $M \ge 1$ there is a natural number $K$ such that every
finite Sidon set $A$ of natural numbers with at least $K$ elements has at least $M$ isolated
elements in $A + A$. -/
def conjecture : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    ∃ K : ℕ, ∀ A : Finset ℕ,
      IsSidon A → K ≤ A.card → M ≤ IsolatedCount (Sumset A)

/--
**Large Sidon sets have many isolated sums.** For every natural number $M \ge 1$ there is a
natural number $K$ such that every finite Sidon set $A$ of natural numbers with at least $K$
elements has at least $M$ isolated elements in its sumset $A + A = \{x + y : x, y \in A\}$. Here
$A$ is a Sidon set when $a + b = c + d$ with $a, b, c, d \in A$ implies $\{a, b\} = \{c, d\}$,
and an element $s$ of $A + A$ is isolated when $s + 1 \notin A + A$ and either $s = 0$ or
$s - 1 \notin A + A$.

This answers Erdős Problem 152 affirmatively: Tsoukalas et al. show, with a Lean proof, that
every Sidon set $A$ of $n$ natural numbers has at least $(n^2 - 100n - 16)/16$ isolated elements
in $A + A$.

Source: George
Tsoukalas et al., Advancing Mathematics Research with AI-Driven Formal Proof Search, arXiv
preprint (2026), arXiv:2605.22763, https://arxiv.org/abs/2605.22763. Moved from
`OpenConjectures/Combinatorics/ErdosSidonIsolatedSums`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosSidonIsolatedSumsWanted
