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

/-- A measure on a complete Boolean algebra in von Neumann's sense (conditions
(1)-(4) are the `CompleteBooleanAlgebra` structure): `μ a = 0` exactly for
`a = ⊥`, `μ a > 0` otherwise, and `μ` is countably additive on pairwise
disjoint sequences. -/
def IsVonNeumannMeasure (B : Type*) [CompleteBooleanAlgebra B] (μ : B → ℝ) : Prop :=
  μ ⊥ = 0 ∧ (∀ a, a ≠ ⊥ → 0 < μ a) ∧
    ∀ a : ℕ → B, (∀ i j, i ≠ j → a i ⊓ a j = ⊥) →
      Summable (fun i => μ (a i)) ∧ μ (⨆ i, a i) = ∑' i, μ (a i)

/-- Condition (5): every subset whose distinct elements are pairwise
disjoint is at most countable (the countable chain condition). -/
def SatisfiesCountableChainCondition (B : Type*) [CompleteBooleanAlgebra B] : Prop :=
  ∀ S : Set B, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ⊓ b = ⊥) → S.Countable

/-- Condition (6), the generalized distributivity law: for each `i`, if
`a₁ⁱ ≤ a₂ⁱ ≤ ...`, then the meet over `i` of the join over `j` of `aⱼⁱ`
equals the join over all choice functions `j(i)` of the meet over `i` of
`a_{j(i)}ⁱ`. -/
def SatisfiesGeneralizedDistributivity (B : Type*) [CompleteBooleanAlgebra B] : Prop :=
  ∀ a : ℕ → ℕ → B, (∀ i, Monotone (a i)) →
    (⨅ i, ⨆ j, a i j) = ⨆ (f : ℕ → ℕ), ⨅ i, a i (f i)

/-- The claim that conditions (5) and (6) together are sufficient for a
measure to exist: every complete Boolean algebra satisfying (5) and (6)
carries a measure in von Neumann's sense. -/
def VonNeumannSufficiencyClaim : Prop :=
  ∀ (B : Type*) [CompleteBooleanAlgebra B],
    SatisfiesCountableChainCondition B → SatisfiesGeneralizedDistributivity B →
      ∃ μ : B → ℝ, IsVonNeumannMeasure B μ

/--
Conditions (5) and (6) together are NOT sufficient for a measure to exist:
there is a complete Boolean algebra satisfying the countable chain condition
and the generalized distributivity law which carries no measure in von
Neumann's sense. This decides the question of Problem 163 in the negative, in
its stated form. The typescript's complement clause prints its two constants
swapped relative to its own usage elsewhere; it is normalized here to the
standard complement laws (bottom `⊥`, top `⊤`).
Source: J. von Neumann, Problem 163 of the Scottish Book; refuted by
M. Talagrand, "Maharam's problem", arXiv:math/0601689 (2006), who
constructed an exhaustive submeasure not equivalent to a measure, solving
the problems of J. von Neumann (1937) and D. Maharam (1947).
-/
theorem_wanted vonNeumannConditionsNotSufficient : ¬ VonNeumannSufficiencyClaim

end MathlibExt.MeasureTheory.ScottishBook163Wanted
