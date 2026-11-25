/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING, p. 239 (comment: "If each task `t` can only be executed by a specified processor
`p(t)`, the problem is NP-complete for `m = 2` and `<` arbitrary, and for `m` arbitrary and `<` a
forest, but can be solved in polynomial time for `m` arbitrary if `<` is a 'cyclic forest'
[Goyal, 1976]"), citing D. K. Goyal, "Scheduling processor bound systems", Technical Report,
Computer Science Department, Washington State University (1976) (not available to this
formalization).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling

open MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance Task taskLength Prec running)

/-!
# PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors is NP-complete

INSTANCE: a set `T` of tasks, each having length `l(t) = 1`, `m = 2` processors, a partial order
`<` on `T`, a deadline `D ∈ ℤ⁺`, and for each task `t ∈ T` a specified processor `p(t)`.
QUESTION: is there an `m`-processor schedule `σ` for `T` that meets the overall deadline `D`,
obeys the precedence constraints, i.e., `t < t'` implies `σ(t') ≥ σ(t) + l(t) = σ(t) + 1`, and
executes each task `t` only on its processor `p(t)`?

This is PRECEDENCE CONSTRAINED SCHEDULING ([SS9], `PrecedenceConstrainedSchedulingWanted`) with
dedicated processors, the variant of the entry's comment, for `m = 2` and `<` arbitrary. The
instance extends the parent's (task lengths, `m`, the pairs `(t, t')` with `t < t'`, `D`) by the
list of the processors `p(t) ∈ {0, …, m - 1}` of the tasks, one per task. The parent's
well-formedness (unit lengths, `m > 0`, the pairs name tasks and form a strict partial order,
`D > 0`), its tasks, lengths, precedence relation and the set `running` of tasks running at a
time are reused. A task executed only on `p(t)` occupies that processor during
`[σ(t), σ(t) + l(t))`, and a processor executes one task at a time, so two different tasks with
the same processor run in disjoint intervals; this implies the parent's bound of `m` tasks
running at a time, which is kept as stated there. `DedicatedWellFormed` and
`DedicatedProcessorsFeasible` state the problem for any `m`; `WellFormed` fixes `m = 2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: a PRECEDENCE CONSTRAINED SCHEDULING instance and the processors `p(t)` of the
tasks, task `t` being the `t`-th entry. -/
abbrev DedicatedProcessorsInstance := PrecedenceConstrainedSchedulingInstance × List ℕ

/-- The processor `p(t)` of task `t`. -/
def processor (i : DedicatedProcessorsInstance) (t : Task i.1) : ℕ :=
  i.2.getD t 0

/-- Well-formedness for any number `m` of processors: the parent's (unit lengths, `m > 0`, the
listed pairs name tasks and form a strict partial order, `D > 0`), one processor per task, and
every processor below `m`. -/
def DedicatedWellFormed (i : DedicatedProcessorsInstance) : Prop :=
  PrecedenceConstrainedScheduling.WellFormed i.1 ∧ i.2.length = i.1.1.length ∧
    ∀ q ∈ i.2, q < i.1.2.1

/-- Some `m`-processor schedule meets the overall deadline `D`, obeys the precedence
constraints, and runs any two different tasks with the same processor in disjoint intervals. -/
def DedicatedProcessorsFeasible (i : DedicatedProcessorsInstance) : Prop :=
  ∃ σ : Task i.1 → ℕ, (∀ u, (running i.1 σ u).card ≤ i.1.2.1) ∧
    (∀ t, σ t + taskLength i.1 t ≤ i.1.2.2.2) ∧
    (∀ t t', Prec i.1 t t' → σ t + taskLength i.1 t ≤ σ t') ∧
    ∀ t t', t ≠ t' → processor i t = processor i t' →
      σ t + taskLength i.1 t ≤ σ t' ∨ σ t' + taskLength i.1 t' ≤ σ t

/-- Well-formedness of an instance: `DedicatedWellFormed` with `m = 2`. -/
def WellFormed (i : DedicatedProcessorsInstance) : Prop :=
  DedicatedWellFormed i ∧ i.1.2.1 = 2

open Classical in
/-- PRECEDENCE CONSTRAINED SCHEDULING on 2 dedicated processors as a decision problem over
bitstrings. -/
noncomputable def twoDedicatedProcessorPrecedenceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := DedicatedProcessorsInstance) x with
  | some i => decide (WellFormed i ∧ DedicatedProcessorsFeasible i)
  | none => false

/-- **PRECEDENCE CONSTRAINED SCHEDULING is NP-complete on 2 dedicated processors.** Source: Garey
and Johnson (1979), [SS9], comment (Goyal, 1976). -/
public theorem_wanted twoDedicatedProcessorPrecedenceScheduling_npComplete :
    twoDedicatedProcessorPrecedenceSchedulingDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoDedicatedProcessorPrecedenceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorPrecedenceScheduling
