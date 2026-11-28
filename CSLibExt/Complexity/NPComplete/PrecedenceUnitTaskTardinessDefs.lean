/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE
WEIGHTED TARDINESS (comment: if precedence constraints are added, the problem is NP-complete
even with equal lengths and equal weights, credited to Lenstra and Rinnooy Kan 1978);
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity of scheduling under precedence
constraints", Operations Research 26 (1978), 22-35, doi:10.1287/opre.26.1.22
(`1|prec, pⱼ = 1|∑ Tⱼ`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness

open SequencingToMinimizeWeightedTardiness (Task taskLength weight deadline
  IsOneProcessorSchedule)

/-- An instance: the [SS5] instance of `SequencingToMinimizeWeightedTardinessDefs` (task
triples `(l(t), w(t), d(t))` and the bound `K`), and the pairs `(t, t')` with `t < t'`. -/
abbrev PrecedenceUnitTaskTardinessInstance :=
  SequencingToMinimizeWeightedTardiness.SequencingToMinimizeWeightedTardinessInstance ×
    List (ℕ × ℕ)

/-- The precedence relation: `t < t'` when the pair `(t, t')` is listed. -/
def Prec (i : PrecedenceUnitTaskTardinessInstance) (t t' : Task i.1) : Prop :=
  ((t : ℕ), (t' : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the [SS5] instance is well-formed, every task has length `1`
and weight `1`, every listed pair names two tasks, and the listed pairs form a strict partial
order. -/
def WellFormed (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  SequencingToMinimizeWeightedTardiness.WellFormed i.1 ∧
    (∀ x ∈ i.1.1, x.1 = 1 ∧ x.2.1 = 1) ∧
    (∀ p ∈ i.2, p.1 < i.1.1.length ∧ p.2 < i.1.1.length) ∧
    IsStrictOrder (Task i.1) (Prec i)

/-- Some one-processor schedule obeys the precedence constraints and has weighted tardiness at
most `K`: the sum, over the tasks with `σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)`
is at most `K`. -/
def PrecedenceUnitTaskTardinessFeasible (i : PrecedenceUnitTaskTardinessInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, IsOneProcessorSchedule (taskLength i.1) σ ∧
    (∀ t t', Prec i t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i.1 t < σ t + taskLength i.1 t),
      (σ t + taskLength i.1 t - deadline i.1 t) * weight i.1 t ≤ i.1.2

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks as a
decision problem over bitstrings. -/
noncomputable def precedenceUnitTaskTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceUnitTaskTardinessInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceUnitTaskTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness
