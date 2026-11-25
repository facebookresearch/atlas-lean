/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Erdős Problem 793: growth of the largest 2-primitive family.

Let `F(n)` be the maximum size of a set `A ⊆ {1, …, n}` such that
no element divides the product of two others: `¬ a ∣ b * c`
whenever `a, b, c ∈ A` with `a ≠ b` and `a ≠ c`.
Is there a constant `C` with
`F(n) = π(n) + (C + o(1)) * n^(2/3) / (log n)^2`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted

/-! Source record `EP-793`. -/

/-- **Sets in which no element divides the product of two others.** A finite set $A$ of natural
numbers is good when every element of $A$ is positive and no $a \in A$ divides $bc$ for any
$b, c \in A$ with $a \ne b$ and $a \ne c$; here $b = c$ is allowed. -/
def Good (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c) ∧ (∀ a ∈ A, 1 ≤ a)

/-- **Maximum size of a good subset.** For a natural number $n$, $F(n)$ is the largest size of a
good subset of $\{1, \dots, n\}$, defined as the supremum of the sizes of the good sets
$A \subseteq \{1, \dots, n\}$. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ Good A ∧ A.card = k}

/-- **Statement of Erdős Problem 793.** For a natural number $n$, let $F(n)$ be the largest size
of a set $A \subseteq \{1, \dots, n\}$ with $a \nmid bc$ for all $a, b, c \in A$ such that
$a \ne b$ and $a \ne c$, and let $\pi(n)$ be the number of primes at most $n$. This is the
proposition that there is a real constant $C > 0$ such that
$(F(n) - \pi(n)) / (n^{2/3} / (\log n)^2) \to C$ as $n \to \infty$.
Equivalently, $F(n) = \pi(n) + (C + o(1))\, n^{2/3} / (\log n)^2$. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ Filter.Tendsto
    (fun n : ℕ => (((F n : ℤ) - (Nat.primeCounting n : ℤ)) : ℝ) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2))
    Filter.atTop (nhds C)

/--
**Erdős Problem 793 has a positive answer.** Let $F(n)$ be the largest size of a set
$A \subseteq \{1, \dots, n\}$ such that $a \nmid bc$ whenever $a, b, c \in A$ with $a \ne b$ and
$a \ne c$ ($b = c$ is allowed), and let $\pi(n)$ be the number of primes at most $n$. Then there
is a real constant $C > 0$ such that $(F(n) - \pi(n)) / (n^{2/3} / (\log n)^2) \to C$ as
$n \to \infty$.

Chojecki (2026, Theorem 1.1) proves this with $C = 27/2$.

Source: P. Chojecki, The Second
Term for Strongly 2-Primitive Sets, arXiv preprint (2026), arXiv:2607.15306,
https://arxiv.org/abs/2607.15306. Moved from
`OpenConjectures/NumberTheory/ErdosDivisibilityFamilyGrowth`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted
