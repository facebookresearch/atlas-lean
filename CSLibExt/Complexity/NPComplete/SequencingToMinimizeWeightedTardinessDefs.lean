/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS: definitions

The definitions that the statements of
`WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted`, and of the wanted
modules built on it, use, moved here unchanged so that their proofs can import them.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-
Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE WEIGHTED TARDINESS; E. L.
Lawler, "A "pseudopolynomial" algorithm for sequencing jobs to minimize total tardiness", Annals of
Discrete Mathematics 1 (1977), 331-342, doi:10.1016/S0167-5060(08)70742-8; J. K. Lenstra, A. H. G.
Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling problems", Annals of Discrete
Mathematics 1 (1977), 343-362, doi:10.1016/S0167-5060(08)70743-X, Theorem 4(d).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness

/-- An instance: the tasks, task `t` being the `t`-th triple `(l(t), w(t), d(t))` of length,
weight and deadline, and the bound `K`. -/
abbrev SequencingToMinimizeWeightedTardinessInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- The tasks of the instance, `Fin n` for `n` listed triples. -/
abbrev Task (i : SequencingToMinimizeWeightedTardinessInstance) : Type := Fin i.1.length

/-- The length `l(t)` of task `t`. -/
def taskLength (i : SequencingToMinimizeWeightedTardinessInstance) (t : Task i) : ℕ :=
  (i.1.get t).1

/-- The weight `w(t)` of task `t`. -/
def weight (i : SequencingToMinimizeWeightedTardinessInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.1

/-- The deadline `d(t)` of task `t`. -/
def deadline (i : SequencingToMinimizeWeightedTardinessInstance) (t : Task i) : ℕ :=
  (i.1.get t).2.2

/-- A one-processor schedule for tasks with lengths `l` (Garey and Johnson, [SS1]): a
one-to-one function `σ` into `ℤ₀⁺` with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`. -/
def IsOneProcessorSchedule {n : ℕ} (l : Fin n → ℕ) (σ : Fin n → ℕ) : Prop :=
  Function.Injective σ ∧ ∀ t t', σ t' < σ t → σ t' + l t' ≤ σ t

/-- Well-formedness of an instance: every length, weight and deadline is positive, and
`K` is positive. -/
def WellFormed (i : SequencingToMinimizeWeightedTardinessInstance) : Prop :=
  (∀ x ∈ i.1, 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2) ∧ 0 < i.2

/-- Some one-processor schedule has weighted tardiness at most `K`: the sum, over the tasks
with `σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is at most `K`. -/
def SequencingToMinimizeWeightedTardinessFeasible
    (i : SequencingToMinimizeWeightedTardinessInstance) : Prop :=
  ∃ σ : Task i → ℕ, IsOneProcessorSchedule (taskLength i) σ ∧
    ∑ t ∈ Finset.univ.filter (fun t => deadline i t < σ t + taskLength i t),
      (σ t + taskLength i t - deadline i t) * weight i t ≤ i.2

open Classical in
/-- SEQUENCING TO MINIMIZE WEIGHTED TARDINESS as a decision problem over bitstrings. -/
noncomputable def sequencingToMinimizeWeightedTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SequencingToMinimizeWeightedTardinessInstance) x with
  | some i => decide (WellFormed i ∧ SequencingToMinimizeWeightedTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
