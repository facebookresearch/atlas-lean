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

/-- Erdős Problem 741, first question (upper-density reading): if `A ⊆ ℕ` and `A + A` has positive
upper density, then `A = A₁ ⊔ A₂` with `A₁ + A₁` and `A₂ + A₂` both of positive upper density. -/
def upperDensitySumsetSplits : Prop :=
  ∀ A : Set ℕ, 0 < (A + A).upperDensity → ∃ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧
    0 < (A₁ + A₁).upperDensity ∧ 0 < (A₂ + A₂).upperDensity

/-- `S ⊆ ℕ` has bounded gaps (is syndetic): some `g` is such that every interval `[n, n + g)`
meets `S`. -/
def HasBoundedGaps (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ s ∈ S, n ≤ s ∧ s < n + g

/-- Erdős Problem 741, second question: there is a basis `A` of order `2` (every sufficiently large
integer is a sum of two elements of `A`) such that for every partition `A = A₁ ⊔ A₂` the sumsets
`A₁ + A₁` and `A₂ + A₂` do not both have bounded gaps. -/
def basisWithoutBoundedGapSplit : Prop :=
  ∃ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 ∧
    ∀ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ → A₁ ∪ A₂ = A →
      ¬ (HasBoundedGaps (A₁ + A₁) ∧ HasBoundedGaps (A₂ + A₂))

/--
Resolved true: erdosproblems.com/741 records DeepMind's positive answer to the upper-density
question: if `A + A` has positive upper density then `A = A₁ ⊔ A₂` with `A₁ + A₁` and `A₂ + A₂` both
of positive upper density (proof sketched in the page's comments; formal-conjectures marks this
statement solved with a formal proof by the DeepMind prover agent, not checked here); the page lists
the problem as solved. Source: T. F. Bloom, Erdős Problems, Problem #741,
https://www.erdosproblems.com/741 (status SOLVED (LEAN)); resolution: B. Alexeev, M. Putterman, M.
Sawhney, M. Sellke and G. Valiant, Short proofs in combinatorics and number theory, arXiv:2603.29961
(2026); erdosproblems.com/741 (DeepMind), Theorem 3.1 of arXiv:2603.29961 (proof due to an internal
OpenAI model): there is A ⊂ ℕ, a basis of order 2 with [4, ∞) ⊆ A + A, such that for every partition
A = A₁ ⊔ A₂ one of A₁ + A₁, A₂ + A₂ does not have bounded gaps; erdosproblems.com/741: DeepMind gave
a positive answer to the upper-density question (proof sketched in the comments),
https://arxiv.org/abs/2603.29961.
-/
public theorem_wanted upperDensitySumsetSplits_holds : upperDensitySumsetSplits

/--
Resolved true: Alexeev, Putterman, Sawhney, Sellke and Valiant (Theorem 3.1, proof by an internal
OpenAI model; DeepMind found a construction independently) give an explicit basis `A` of order `2`
such that for every partition `A = A₁ ⊔ A₂` one of `A₁ + A₁`, `A₂ + A₂` does not have bounded gaps.
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
