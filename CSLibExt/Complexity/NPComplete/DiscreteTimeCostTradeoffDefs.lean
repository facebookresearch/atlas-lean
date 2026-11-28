/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISCRETE TIME-COST TRADEOFF: definitions

Source:
P. De, E. J. Dunne, J. B. Ghosh, and C. E. Wells, "Complexity of the discrete time-cost
tradeoff problem for project networks", Operations Research 45 (1997), 302-306,
doi:10.1287/opre.45.2.302 (Section 2: the DTCT decision problem is strongly NP-hard, by a
reduction from EXACTLY-ONE-IN-THREE 3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DiscreteTimeCostTradeoff

/-- An instance: the number `n` of activities, the precedence arcs `(u, v)` among them, for
each activity `v` the list of its alternatives `(t(v, j), c(v, j))`, the due date `d`, and the
budget `b`. -/
abbrev DiscreteTimeCostTradeoffInstance :=
  ℕ × List (ℕ × ℕ) × List (List (ℕ × ℕ)) × ℕ × ℕ

/-- The alternatives `(time, cost)` of activity `v`. -/
def alternatives (i : DiscreteTimeCostTradeoffInstance) (v : ℕ) : List (ℕ × ℕ) :=
  i.2.2.1.getD v []

/-- The time of activity `v` under the realization `σ` (alternative `σ v` chosen). -/
def time (i : DiscreteTimeCostTradeoffInstance) (σ : ℕ → ℕ) (v : ℕ) : ℕ :=
  ((alternatives i v).getD (σ v) (0, 0)).1

/-- The cost of activity `v` under the realization `σ`. -/
def cost (i : DiscreteTimeCostTradeoffInstance) (σ : ℕ → ℕ) (v : ℕ) : ℕ :=
  ((alternatives i v).getD (σ v) (0, 0)).2

/-- Well-formedness of an instance: every arc `(u, v)` joins activities with `u < v < n` (the
source's numbering of the nodes), there is one alternative list per activity, and every
alternative list is nonempty with strictly increasing times and strictly decreasing costs. -/
def WellFormed (i : DiscreteTimeCostTradeoffInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < a.2 ∧ a.2 < i.1) ∧ i.2.2.1.length = i.1 ∧
    ∀ l ∈ i.2.2.1, l ≠ [] ∧ l.Pairwise fun x y => x.1 < y.1 ∧ y.2 < x.2

/-- The early finish time of the project under `σ` is at most `d`: some start times `S`
(nonnegative, after the dummy start) respect every precedence arc and let every activity
complete by `d` (before the dummy finish). -/
def EarlyFinishAtMost (i : DiscreteTimeCostTradeoffInstance) (σ : ℕ → ℕ) (d : ℕ) : Prop :=
  ∃ S : ℕ → ℕ, (∀ a ∈ i.2.1, S a.1 + time i σ a.1 ≤ S a.2) ∧
    ∀ v < i.1, S v + time i σ v ≤ d

/-- Some realization `σ` (an alternative `σ v` of every activity `v`) has early finish time
at most `d` and cost at most `b`. -/
def DiscreteTimeCostTradeoffFeasible (i : DiscreteTimeCostTradeoffInstance) : Prop :=
  ∃ σ : ℕ → ℕ, (∀ v < i.1, σ v < (alternatives i v).length) ∧
    EarlyFinishAtMost i σ i.2.2.2.1 ∧ ∑ v ∈ Finset.range i.1, cost i σ v ≤ i.2.2.2.2

open Classical in
/-- DISCRETE TIME-COST TRADEOFF as a decision problem over bitstrings. -/
noncomputable def discreteTimeCostTradeoffDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DiscreteTimeCostTradeoffInstance) x with
  | some i => decide (WellFormed i ∧ DiscreteTimeCostTradeoffFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DiscreteTimeCostTradeoff
