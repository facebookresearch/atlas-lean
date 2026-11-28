/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING;
J. D. Ullman, "NP-complete scheduling problems", Journal of Computer and System Sciences 10
(1975), 384-393, doi:10.1016/S0022-0000(75)80008-0.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling

/-- An instance: the task lengths `l(t)` (task `t` is the `t`-th entry; all must be `1`), the
number `m` of processors, the pairs `(t, t')` with `t < t'`, and the deadline `D`. -/
abbrev PrecedenceConstrainedSchedulingInstance := List ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed lengths. -/
abbrev Task (i : PrecedenceConstrainedSchedulingInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : PrecedenceConstrainedSchedulingInstance) (t : Task i) : ℕ :=
  i.1.get t

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : PrecedenceConstrainedSchedulingInstance) (t t' : Task i) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2.2.1

/-- The tasks running at time `u` under `σ`: those with `σ(t) ≤ u < σ(t) + l(t)`. -/
def running (i : PrecedenceConstrainedSchedulingInstance) (σ : Task i → ℕ) (u : ℕ) :
    Finset (Task i) :=
  Finset.univ.filter fun t => σ t ≤ u ∧ u < σ t + taskLength i t

/-- Well-formedness of an instance: every task has length `1`, `m` is positive, every listed
pair names two tasks, the listed pairs form a strict partial order, and `D` is positive. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  (∀ l ∈ i.1, l = 1) ∧ 0 < i.2.1 ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Task i) (Prec i) ∧ 0 < i.2.2.2

/-- Some `m`-processor schedule meets the overall deadline `D` and obeys the precedence
constraints. -/
def PrecedenceConstrainedSchedulingFeasible (i : PrecedenceConstrainedSchedulingInstance) :
    Prop :=
  ∃ σ : Task i → ℕ, (∀ u, (running i σ u).card ≤ i.2.1) ∧
    (∀ t, σ t + taskLength i t ≤ i.2.2.2) ∧
    ∀ t t', Prec i t t' → σ t + taskLength i t ≤ σ t'

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING as a decision problem over bitstrings. -/
noncomputable def precedenceConstrainedSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
