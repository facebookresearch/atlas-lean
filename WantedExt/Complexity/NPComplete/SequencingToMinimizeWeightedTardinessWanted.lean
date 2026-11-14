/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS5] SEQUENCING TO MINIMIZE
WEIGHTED TARDINESS;
E. L. Lawler, "A "pseudopolynomial" algorithm for sequencing jobs to minimize total
tardiness", Annals of Discrete Mathematics 1 (1977), 331-342,
doi:10.1016/S0167-5060(08)70742-8;
J. K. Lenstra, A. H. G. Rinnooy Kan, and P. Brucker, "Complexity of machine scheduling
problems", Annals of Discrete Mathematics 1 (1977), 343-362,
doi:10.1016/S0167-5060(08)70743-X, Theorem 4(d).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness

/-!
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete

INSTANCE: a set `T` of tasks, for each task `t ∈ T` a length `l(t) ∈ ℤ⁺`, a weight
`w(t) ∈ ℤ⁺` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`. QUESTION: is there a
one-processor schedule `σ` for `T` such that the sum, taken over all `t ∈ T` satisfying
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is `K` or less?

A one-processor schedule (Garey and Johnson, [SS1]) is a one-to-one function `σ : T → ℤ₀⁺`
with `σ(t) > σ(t')` implying `σ(t) ≥ σ(t') + l(t')`. The tasks are `Fin n`, one per listed
triple `(l(t), w(t), d(t))`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SEQUENCING TO MINIMIZE WEIGHTED TARDINESS is NP-complete.** Source: Garey and Johnson
(1979), [SS5]; Lawler (1977); Lenstra, Rinnooy Kan, and Brucker (1977), Theorem 4(d). -/
public theorem_wanted sequencingToMinimizeWeightedTardiness_npComplete :
    sequencingToMinimizeWeightedTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sequencingToMinimizeWeightedTardinessDec

end MetaMathlibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardiness
