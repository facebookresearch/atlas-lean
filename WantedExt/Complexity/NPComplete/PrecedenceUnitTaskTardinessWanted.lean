/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
# NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness

open SequencingToMinimizeWeightedTardiness (Task taskLength weight deadline
  IsOneProcessorSchedule)

/-!
# SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
# NP-complete

INSTANCE: a set `T` of tasks, a partial order `<` on `T`, for each task `t ∈ T` a length
`l(t) = 1`, a weight `w(t) = 1` and a deadline `d(t) ∈ ℤ⁺`, and a positive integer `K`.
QUESTION: is there a one-processor schedule `σ` for `T` that obeys the precedence constraints
(`t < t'` implies `σ(t) + l(t) ≤ σ(t')`) such that the sum, taken over all `t ∈ T` satisfying
`σ(t) + l(t) > d(t)`, of `(σ(t) + l(t) - d(t)) · w(t)` is `K` or less?

This is SEQUENCING TO MINIMIZE WEIGHTED TARDINESS ([SS5]) with precedence constraints added and
all lengths and weights equal to `1` (`1|prec, pⱼ = 1|∑ Tⱼ`, the case Lenstra and Rinnooy Kan
prove). The [SS5] instance (tasks as `(l(t), w(t), d(t))` triples and the bound `K`), its
well-formedness, the task accessors and the one-processor schedule predicate are reused from
`SequencingToMinimizeWeightedTardinessWanted`. The partial order is given by the list of its
pairs `(t, t')` with `t < t'`, required to be a strict order (Mathlib's `IsStrictOrder`:
irreflexive and transitive). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the [SS5] instance of `SequencingToMinimizeWeightedTardinessWanted` (task
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

/-- **SEQUENCING TO MINIMIZE WEIGHTED TARDINESS with precedence constraints and unit tasks is
NP-complete.** Source: Garey and Johnson (1979), [SS5]; Lenstra and Rinnooy Kan (1978). -/
public theorem_wanted precedenceUnitTaskTardiness_npComplete :
    precedenceUnitTaskTardinessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceUnitTaskTardinessDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceUnitTaskTardiness
