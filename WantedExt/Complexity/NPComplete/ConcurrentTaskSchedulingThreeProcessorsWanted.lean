/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONCURRENT TASK SCHEDULING ON THREE PROCESSORS is NP-complete

Source:
E. L. Lloyd, "Concurrent task systems", Operations Research 29 (1981), 189-201,
doi:10.1287/opre.29.1.189 (abstract: a concurrent task system "consists of: m identical
processors, tasks T₁, …, Tₙ, and a partial order on those tasks which represents precedence
constraints. Associated with each task Tᵢ is a positive integral execution time τᵢ and a degree
of concurrency qᵢ ∈ 𝒞 where 𝒞 ⊆ {1, …, m}. Task Tᵢ must execute for τᵢ steps and for each of
those τᵢ steps it requires qᵢ processors. ... we show that scheduling concurrent UET task
systems is NP-complete even if there are only three processors and each task has a degree of
concurrency of either 1 or 2"; the full text was not available to us);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problems [SS9] PRECEDENCE CONSTRAINED SCHEDULING (every
degree `1`) and [SS10] RESOURCE CONSTRAINED SCHEDULING (the model with precedence used here).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBoundWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConcurrentTaskSchedulingThreeProcessors

open ResourceConstrainedScheduling (Task req bound)
open ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed PrecedenceFeasible)

/-!
# CONCURRENT TASK SCHEDULING ON THREE PROCESSORS is NP-complete

INSTANCE: `m = 3` identical processors, a set `T` of tasks, each with execution time `1` (a
concurrent UET task system) and a degree of concurrency `q(t) ∈ {1, 2}`, a partial order `<` on
`T` (precedence constraints), and a deadline `D ∈ ℤ⁺`. QUESTION: is there a schedule of length
at most `D`, i.e. a start time `σ(t) ∈ ℤ₀⁺` for each task such that `σ(t) + 1 ≤ D`, `t < t'`
implies `σ(t) + 1 ≤ σ(t')`, and at every time step the degrees of the tasks executing sum to at
most `3`?

A task of degree `q` requires `q` of the identical processors during each step of its execution,
so the processors act as one resource with bound `m` and the degree is the task's requirement.
The problem is therefore RESOURCE CONSTRAINED SCHEDULING with a partial order
(`PrecedenceResourceSchedulingInstance`, `PrecedenceWellFormed` and `PrecedenceFeasible` of
`ResourceConstrainedSchedulingPrecedenceZeroOrBoundWanted`, unit tasks as in [SS10] and
precedence as in [SS9]) with `m = 3` processors, `r = 1` resource of bound `B_1 = 3`, and every
requirement `R_1(t) = q(t) ∈ {1, 2}`. That model also bounds the number of running tasks by
`m`; with every requirement at least `1` this follows from the resource bound, so it adds no
constraint. Lloyd also solves the case `m = 2` in polynomial time. Numbers use the binary
encoding (they are bounded by the input size up to the deadline, so the problem is NP-complete
in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order (unit tasks, a strict partial order, a positive deadline), with `m = 3`
processors, `r = 1` resource of bound `B_1 = 3` (the processors), and every task's degree of
concurrency `R_1(t)` equal to `1` or `2`. -/
def WellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  PrecedenceWellFormed i ∧ i.1.1 = 3 ∧ i.1.2.1 = 1 ∧ bound i.1 0 = 3 ∧
    ∀ t : Task i.1, req i.1 t 0 = 1 ∨ req i.1 t 0 = 2

open Classical in
/-- CONCURRENT TASK SCHEDULING ON THREE PROCESSORS as a decision problem over bitstrings. -/
noncomputable def concurrentTaskSchedulingThreeProcessorsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceResourceSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceFeasible i)
  | none => false

/-- **CONCURRENT TASK SCHEDULING ON THREE PROCESSORS is NP-complete.** Source: Lloyd (1981);
Garey and Johnson (1979), [SS9] (every degree `1`), [SS10]. -/
public theorem_wanted concurrentTaskSchedulingThreeProcessors_npComplete :
    concurrentTaskSchedulingThreeProcessorsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L concurrentTaskSchedulingThreeProcessorsDec

end MetaMathlibExt.Complexity.NPComplete.ConcurrentTaskSchedulingThreeProcessors
