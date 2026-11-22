/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Splitting sets with dense or syndetic sumsets (Erdős Problem 741)

Erdős Problem 741 (Burr and Erdős): let `A ⊆ ℕ` be such that `A + A` has positive (upper) density.
Can one always decompose `A = A₁ ⊔ A₂` such that `A₁ + A₁` and `A₂ + A₂` both have positive (upper)
density? Is there a basis `A` of order `2` such that if `A = A₁ ⊔ A₂` then `A₁ + A₁` and `A₂ + A₂`
cannot both have bounded gaps?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import MathlibExt.Combinatorics.Additive.Basis
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #741, https://www.erdosproblems.com/741 (status SOLVED
(LEAN)). UnsolvedMath record UM-00002288 (`EP-741`), dataset ulamai/UnsolvedMath v1.8.0.

Upper density is MathlibExt's `Set.upperDensity`; the first question is stated for upper density,
the reading the problem page says captures its spirit (the version where the densities must exist
was answered negatively and is not formalized). A basis of order `2` is read asymptotically,
MathlibExt's `Set.IsAsymptoticAddBasisOfOrder A 2` (all but finitely many integers lie in `2 • A = A
+ A`), as in the resolving paper. Bounded gaps: some `g` with every interval `[n, n + g)` meeting
the set. Both answers are machine-generated (DeepMind; an internal OpenAI model); the problem page
states both answers and marks the problem solved. Compared with the formal-conjectures statement
`ErdosProblems/741.lean` (first question equivalent, marked solved there with a formal proof by the
DeepMind prover agent; the basis there is `A ∪ {0}` of exact order 2; no code imported).
-/

open scoped Pointwise

/-- **Erdős Problem 741, upper-density question.** This proposition asserts that for every set
$A \subseteq \mathbb{N}$ whose sumset $A + A = \{a + b : a, b \in A\}$ has positive upper density
there are disjoint sets $A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$ such that both
$A_1 + A_1$ and $A_2 + A_2$ have positive upper density. -/
def upperDensitySumsetSplits : Prop :=
  ∀ A : Set ℕ, 0 < (A + A).upperDensity → ∃ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧
    0 < (A₁ + A₁).upperDensity ∧ 0 < (A₂ + A₂).upperDensity

/-- **Sets with bounded gaps.** A set $S \subseteq \mathbb{N}$ has bounded gaps (is syndetic) if
there is a natural number $g$ such that for every natural number $n$ some $s \in S$ satisfies
$n \le s < n + g$. -/
def HasBoundedGaps (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ s ∈ S, n ≤ s ∧ s < n + g

/-- **Erdős Problem 741, bounded-gaps question.** This proposition asserts that there is a set
$A \subseteq \mathbb{N}$ that is an asymptotic additive basis of order $2$ (all but finitely many
natural numbers are sums of two elements of $A$) such that for all disjoint sets
$A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$, the sumsets
$A_1 + A_1 = \{a + b : a, b \in A_1\}$ and $A_2 + A_2$ do not both have bounded gaps. -/
def basisWithoutBoundedGapSplit : Prop :=
  ∃ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 ∧
    ∀ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ → A₁ ∪ A₂ = A →
      ¬ (HasBoundedGaps (A₁ + A₁) ∧ HasBoundedGaps (A₂ + A₂))

/-- **Splitting a set whose sumset has positive upper density.** For every set
$A \subseteq \mathbb{N}$ whose sumset $A + A = \{a + b : a, b \in A\}$ has positive upper density,
there are disjoint sets $A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$ such that both
$A_1 + A_1$ and $A_2 + A_2$ have positive upper density.

Source: T. F. Bloom, Erdős Problems, Problem #741,
https://www.erdosproblems.com/741 (status SOLVED (LEAN)); resolution: B. Alexeev, M. Putterman, M.
Sawhney, M. Sellke and G. Valiant, Short proofs in combinatorics and number theory, arXiv:2603.29961
(2026); erdosproblems.com/741 (DeepMind), Theorem 3.1 of arXiv:2603.29961 (proof due to an internal
OpenAI model): there is A ⊂ ℕ, a basis of order 2 with [4, ∞) ⊆ A + A, such that for every partition
A = A₁ ⊔ A₂ one of A₁ + A₁, A₂ + A₂ does not have bounded gaps; erdosproblems.com/741: DeepMind gave
a positive answer to the upper-density question (proof sketched in the comments),
https://arxiv.org/abs/2603.29961.
-/
public theorem_wanted upperDensitySumsetSplits_holds : upperDensitySumsetSplits

/-- **An asymptotic basis of order 2 admitting no bounded-gap splitting.** There is a set
$A \subseteq \mathbb{N}$ that is an asymptotic additive basis of order $2$ (all but finitely many
natural numbers are sums of two elements of $A$) such that for all disjoint sets
$A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$, the sumsets
$A_1 + A_1 = \{a + b : a, b \in A_1\}$ and $A_2 + A_2$ do not both have bounded gaps, where a set
$S \subseteq \mathbb{N}$ has bounded gaps if for some $g \in \mathbb{N}$ every interval
$[n, n + g)$ with $n \in \mathbb{N}$ meets $S$.

Source: T. F. Bloom, Erdős Problems, Problem #741, https://www.erdosproblems.com/741 (status SOLVED
(LEAN)); resolution: B. Alexeev, M. Putterman, M. Sawhney, M. Sellke and G. Valiant, Short proofs in
combinatorics and number theory, arXiv:2603.29961 (2026); erdosproblems.com/741 (DeepMind), Theorem
3.1 of arXiv:2603.29961 (proof due to an internal OpenAI model): there is A ⊂ ℕ, a basis of order 2
with [4, ∞) ⊆ A + A, such that for every partition A = A₁ ⊔ A₂ one of A₁ + A₁, A₂ + A₂ does not have
bounded gaps; erdosproblems.com/741: DeepMind gave a positive answer to the upper-density question
(proof sketched in the comments), https://arxiv.org/abs/2603.29961.
-/
public theorem_wanted basisWithoutBoundedGapSplit_holds : basisWithoutBoundedGapSplit

end MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
