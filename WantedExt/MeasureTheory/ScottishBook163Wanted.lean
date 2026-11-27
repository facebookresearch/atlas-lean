/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.MeasureTheory.ScottishBook163Wanted

/-- **Von Neumann measures on a complete Boolean algebra.** A real-valued function $\mu$ on a
complete Boolean algebra $B$ is a measure in von Neumann's sense when $\mu(\bot) = 0$,
$\mu(a) > 0$ for every $a \ne \bot$, and $\mu$ is countably additive: for every sequence
$(a_i)_{i \in \mathbb{N}}$ of pairwise disjoint elements of $B$ (that is, $a_i \wedge a_j = \bot$
whenever $i \ne j$), the series $\sum_i \mu(a_i)$ converges and
$\mu(\bigvee_i a_i) = \sum_i \mu(a_i)$.

Von Neumann's conditions (1)-(4) are the axioms of a complete Boolean algebra. -/
def IsVonNeumannMeasure (B : Type*) [CompleteBooleanAlgebra B] (μ : B → ℝ) : Prop :=
  μ ⊥ = 0 ∧ (∀ a, a ≠ ⊥ → 0 < μ a) ∧
    ∀ a : ℕ → B, (∀ i j, i ≠ j → a i ⊓ a j = ⊥) →
      Summable (fun i => μ (a i)) ∧ μ (⨆ i, a i) = ∑' i, μ (a i)

/-- **The countable chain condition for complete Boolean algebras.** A complete Boolean algebra
$B$ satisfies the countable chain condition (von Neumann's condition (5)) when every subset
$S \subseteq B$ whose distinct elements are pairwise disjoint (that is, $a \wedge b = \bot$ for
all distinct $a, b \in S$) is at most countable. -/
def SatisfiesCountableChainCondition (B : Type*) [CompleteBooleanAlgebra B] : Prop :=
  ∀ S : Set B, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ⊓ b = ⊥) → S.Countable

/-- **Von Neumann's generalized distributivity law.** A complete Boolean algebra $B$ satisfies
the generalized distributivity law (von Neumann's condition (6)) when, for every double sequence
$(a_{i,j})_{i, j \in \mathbb{N}}$ of elements of $B$ that is increasing in $j$ for each fixed $i$
(that is, $a_{i,0} \le a_{i,1} \le \cdots$ for every $i$),
$$\bigwedge_{i} \bigvee_{j} a_{i,j} = \bigvee_{f} \bigwedge_{i} a_{i,f(i)},$$
where $f$ ranges over all functions $\mathbb{N} \to \mathbb{N}$. -/
def SatisfiesGeneralizedDistributivity (B : Type*) [CompleteBooleanAlgebra B] : Prop :=
  ∀ a : ℕ → ℕ → B, (∀ i, Monotone (a i)) →
    (⨅ i, ⨆ j, a i j) = ⨆ (f : ℕ → ℕ), ⨅ i, a i (f i)

/-- **Von Neumann's sufficiency claim.** The statement that every complete Boolean algebra
satisfying the countable chain condition and the generalized distributivity law carries a
measure in von Neumann's sense. -/
def VonNeumannSufficiencyClaim : Prop :=
  ∀ (B : Type*) [CompleteBooleanAlgebra B],
    SatisfiesCountableChainCondition B → SatisfiesGeneralizedDistributivity B →
      ∃ μ : B → ℝ, IsVonNeumannMeasure B μ

/--
**Von Neumann's conditions do not guarantee a measure.** There is a complete Boolean algebra that
satisfies the countable chain condition and the generalized distributivity law but carries no
measure in von Neumann's sense; that is, von Neumann's sufficiency claim is false. This answers
Problem 163 of the Scottish Book in the negative, in its stated form.

The typescript's complement clause prints its two constants swapped relative to its own usage
elsewhere; it is read here as the standard complement laws, with bottom $\bot$ and top $\top$.

Source: J. von Neumann, Problem 163 of the Scottish Book; refuted by
M. Talagrand, "Maharam's problem", arXiv:math/0601689 (2006), who
constructed an exhaustive submeasure not equivalent to a measure, solving
the problems of J. von Neumann (1937) and D. Maharam (1947).
-/
theorem_wanted vonNeumannConditionsNotSufficient : ¬ VonNeumannSufficiencyClaim

end MathlibExt.MeasureTheory.ScottishBook163Wanted
