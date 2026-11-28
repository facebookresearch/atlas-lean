/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTICAL PARALLEL MACHINE SCHEDULING P2|chains|Cmax: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainPrecedenceScheduling

open PrecedenceConstrainedScheduling
  (PrecedenceConstrainedSchedulingInstance PrecedenceConstrainedSchedulingFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorChainPrecedenceScheduling
