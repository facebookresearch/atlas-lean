/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIVE-PROCESSOR TASKS, MAKESPAN `P5|size_i|C_max` is NP-complete

Source:
J. Du and J. Y.-T. Leung, "Complexity of scheduling parallel task systems", SIAM Journal on
Discrete Mathematics 2 (1989), 473-487, doi:10.1137/0402042 (only the abstract was available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P5|size_i|C_max` (minimal NP-hard in the
strong sense, citing Du and Leung 1989).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RCPSPWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan

open RCPSP (RCPSPInstance RCPSPFeasible)

/-!
# FIVE-PROCESSOR TASKS, MAKESPAN `P5|size_i|C_max` is NP-complete

INSTANCE: five identical processors, each executing at most one task at a time; `n` independent
tasks, task `i` with a processing time `p_i ∈ ℤ⁺` and a size `size_i ∈ {1, …, 5}` (the task
uses `size_i` processors, any of them, simultaneously during its whole uninterrupted
processing); and a bound `K`. QUESTION: is there a schedule with makespan `max_i C_i ≤ K`,
where `C_i` is the completion time of task `i`?

Du and Leung prove that scheduling independent parallel tasks to minimize the schedule length is
NP-hard in the strong sense for five processors. The Brucker-Knust tables record
`P5|size_i|C_max` as minimal NP-hard in the strong sense, credited to Du and Leung.

Encoding. The instance is a RESOURCE-CONSTRAINED PROJECT SCHEDULING instance
(`RCPSPWanted`) with no precedence pairs and resource capacity `5`: the tasks are listed one
per entry as `(p_i, size_i)`, and the bound `K` is that module's deadline. Its feasibility,
`RCPSPFeasible`, asks for natural start times with every task completed by `K` and, at every
time before `K`, total size of the running tasks at most the capacity. Processors are not
named: start times admit an assignment of processors, each task keeping its processors
throughout its processing, exactly when at every time the sizes of the running tasks sum to at
most `5` (replacing each task by `size_i` copies of its interval gives an interval graph, whose
chromatic number is its largest clique). Natural start times lose no generality: rounding all
start times down keeps the capacity (two tasks that do not overlap still do not, and pairwise
overlapping intervals share a point) and does not increase the makespan. Membership in NP is
the certificate argument: the `n` start times, each at most `K`, are checked in polynomial
time (the running set changes only at the `2n` start and completion times). Numbers use the
binary encoding (the problem is NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed RESOURCE-CONSTRAINED PROJECT SCHEDULING
instance with no precedence pairs and capacity `5` (the five processors), every task having a
positive processing time and size `1 ≤ size_i ≤ 5`. -/
def WellFormed (i : RCPSPInstance) : Prop :=
  RCPSP.WellFormed i ∧ i.2.1 = [] ∧ i.2.2.1 = 5 ∧ ∀ t ∈ i.1, 0 < t.1 ∧ 1 ≤ t.2 ∧ t.2 ≤ 5

open Classical in
/-- `P5|size_i|C_max` as a decision problem over bitstrings. -/
noncomputable def fiveProcessorTaskSizeMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := RCPSPInstance) x with
  | some i => decide (WellFormed i ∧ RCPSPFeasible i)
  | none => false

/-- **FIVE-PROCESSOR TASKS, MAKESPAN `P5|size_i|C_max` is NP-complete.** Source: Du and Leung
(1989), as recorded in the Brucker-Knust classification. -/
public theorem_wanted fiveProcessorTaskSizeMakespan_npComplete :
    fiveProcessorTaskSizeMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fiveProcessorTaskSizeMakespanDec

end MetaMathlibExt.Complexity.NPComplete.FiveProcessorTaskSizeMakespan
