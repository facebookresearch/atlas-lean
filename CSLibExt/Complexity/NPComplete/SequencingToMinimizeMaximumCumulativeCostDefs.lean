/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS7] SEQUENCING TO MINIMIZE
MAXIMUM CUMULATIVE COST (reference: [Abdel-Wahab, 1976], transformation from REGISTER SUFFICIENCY);
H. M. Abdel-Wahab, *Scheduling with Applications to Register Allocation and Deadlock Problems*,
Ph.D. thesis, University of Waterloo (1976) (not available to this formalization);
H. M. Abdel-Wahab and T. Kameda, "Scheduling to minimize maximum cumulative cost subject to
series-parallel precedence constraints", Operations Research 26 (1978), 141-158,
doi:10.1287/opre.26.1.141.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost

/-- An instance: the costs `c(0), …, c(n - 1)` as pairs `(p, q)` standing for `p - q`, the pairs
`(t, t')` with `t < t'`, and the bound `K` as a pair `(p, q)` standing for `p - q`. -/
abbrev SequencingToMinimizeMaximumCumulativeCostInstance :=
  List (ℕ × ℕ) × List (ℕ × ℕ) × (ℕ × ℕ)

/-- The tasks of the instance, `Fin n` for `n` listed costs. -/
abbrev Task (i : SequencingToMinimizeMaximumCumulativeCostInstance) : Type := Fin i.1.length

/-- The cost `c(t) ∈ ℤ` of task `t`. -/
def cost (i : SequencingToMinimizeMaximumCumulativeCostInstance) (t : Task i) : ℤ :=
  ((i.1.get t).1 : ℤ) - ((i.1.get t).2 : ℤ)

/-- The bound `K ∈ ℤ`. -/
def bound (i : SequencingToMinimizeMaximumCumulativeCostInstance) : ℤ :=
  (i.2.2.1 : ℤ) - (i.2.2.2 : ℤ)

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : SequencingToMinimizeMaximumCumulativeCostInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: every listed pair names two tasks, and the listed pairs form
a strict partial order. -/
def WellFormed (i : SequencingToMinimizeMaximumCumulativeCostInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Task i) (Prec i)

/-- Some order `σ` of the tasks obeys the precedence constraints, and for every task `t` the
costs of the tasks `t'` with `σ(t') ≤ σ(t)` sum to at most `K`. -/
def SequencingToMinimizeMaximumCumulativeCostFeasible
    (i : SequencingToMinimizeMaximumCumulativeCostInstance) : Prop :=
  ∃ σ : Task i → ℕ, Function.Injective σ ∧ (∀ t t', Prec i t t' → σ t < σ t') ∧
    ∀ t, ((Finset.univ.filter fun t' => σ t' ≤ σ t).sum fun t' => cost i t') ≤ bound i

open Classical in
/-- SEQUENCING TO MINIMIZE MAXIMUM CUMULATIVE COST as a decision problem over bitstrings. -/
noncomputable def sequencingToMinimizeMaximumCumulativeCostDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeMaximumCumulativeCostInstance) x with
  | some i => decide (WellFormed i ∧ SequencingToMinimizeMaximumCumulativeCostFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeMaximumCumulativeCost
