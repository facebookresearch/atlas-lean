/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTICAL PARALLEL MACHINE SCHEDULING P2|chains|Cmax is NP-complete

Source:
J. Du, J. Y.-T. Leung, and G. H. Young, "Scheduling chain-structured tasks to minimize makespan
and mean flow time", Information and Computation 92 (1991), 219-236,
doi:10.1016/0890-5401(91)90009-Q (minimizing the makespan of a nonpreemptive schedule of chains
on `m` identical processors is NP-hard in the strong sense for each fixed `m > 1`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Parallel machine problems without preemption" (`P2|chains|C_max`, minimal NP-hard in the
strong sense, credited to Du, Leung, and Young 1991);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problems [SS8] MULTIPROCESSOR SCHEDULING and
[SS9] PRECEDENCE CONSTRAINED SCHEDULING (the `m`-processor schedule and the parent problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.F3UnitChainsLateJobsWanted
public import WantedExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainPrecedenceScheduling

open PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance PrecedenceConstrainedSchedulingFeasible)

/-!
# IDENTICAL PARALLEL MACHINE SCHEDULING P2|chains|Cmax is NP-complete

INSTANCE: a set `T` of tasks, each having a length `l(t) ∈ ℤ⁺`, `m = 2` identical processors, a
precedence relation on `T` consisting of disjoint chains (each task has at most one immediate
predecessor and at most one immediate successor), and a deadline `D ∈ ℤ⁺`. QUESTION: is there a
two-processor schedule `σ` for `T` that meets the overall deadline `D` (makespan `C_max ≤ D`) and
obeys the precedence constraints, i.e., such that `t` preceding `t'` implies
`σ(t') ≥ σ(t) + l(t)`?

This is Brucker and Knust's `P2|chains|C_max`; Du, Leung, and Young (1991) prove it NP-hard in the
strong sense (for every fixed number `m > 1` of processors). It is PRECEDENCE CONSTRAINED
SCHEDULING ([SS9], `PrecedenceConstrainedSchedulingWanted`) with `m = 2`, positive task lengths
in place of unit lengths, and chain precedences. The instance type (the task lengths, `m`, a list
of task pairs, `D`) and the feasibility are that module's: an `m`-processor schedule in the sense
of [SS8] (at every time `u` at most `m` tasks `t` with `σ(t) ≤ u < σ(t) + l(t)`), every task
ending by `D`, and `σ(t) + l(t) ≤ σ(t')` for every listed pair `(t, t')`. Here the listed pairs
are the arcs of the chains (`t` the immediate predecessor of `t'`) rather than the whole order:
`WellFormed` asks for `m = 2`, positive lengths (as in [SS8], `MultiprocessorSchedulingWanted`),
arcs forming chains on the tasks (`F3UnitChainsLateJobs.ChainsWellFormed`: distinct arcs naming
tasks, no task with two immediate successors or two immediate predecessors, no cycle) and
`0 < D`. The precedence relation
is the transitive closure of the arcs; respecting every arc respects every pair of it. Tasks are
`Fin n`. Binary encoding of all numbers. Membership in NP is the certificate argument: the `n`
start times, each at most `D`, are checked in polynomial time (only the `O(n)` start and end times
need to be inspected for the processor bound).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: `m = 2`, every task length is positive, the listed pairs are
the arcs of disjoint chains on the tasks (distinct arcs naming tasks, no task with two immediate
successors or two immediate predecessors, no cycle), and `D` is positive. -/
def WellFormed (i : PrecedenceConstrainedSchedulingInstance) : Prop :=
  i.2.1 = 2 ∧ (∀ l ∈ i.1, 0 < l) ∧ F3UnitChainsLateJobs.ChainsWellFormed i.1.length i.2.2.1 ∧
    0 < i.2.2.2

open Classical in
/-- IDENTICAL PARALLEL MACHINE SCHEDULING P2|chains|Cmax as a decision problem over
bitstrings. -/
noncomputable def twoProcessorChainPrecedenceSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceConstrainedSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceConstrainedSchedulingFeasible i)
  | none => false

/-- **IDENTICAL PARALLEL MACHINE SCHEDULING P2|chains|Cmax is NP-complete.** Source: Du, Leung,
and Young (1991); Brucker and Knust's classification (`P2|chains|C_max`). -/
public theorem_wanted twoProcessorChainPrecedenceScheduling_npComplete :
    twoProcessorChainPrecedenceSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorChainPrecedenceSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainPrecedenceScheduling
