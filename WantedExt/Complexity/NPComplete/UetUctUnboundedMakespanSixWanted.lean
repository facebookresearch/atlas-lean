/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6 is NP-complete

Source:
J. A. Hoogeveen, J. K. Lenstra and B. Veltman, "Three, four, five, six, or the complexity of
scheduling with communication delays", Operations Research Letters 16 (1994), 129-137,
doi:10.1016/0167-6377(94)90024-8 (problem `P̄|prec,c=1,p_j=1|C_max`, schedule of length at most
6; Theorem 4 of the preprint, CWI Report BS-R9229, 1992).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UetUctSchedulingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UetUctUnboundedMakespanSix

open MetaMathlibExt.Complexity.NPComplete.UetUctScheduling (UetUctSchedulingInstance)

/-!
# UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6 is NP-complete

INSTANCE: `n` jobs, each with processing time one, a precedence relation given by an acyclic
directed graph `G` on the jobs, and identical parallel machines whose number does not restrict
the schedule (`P̄`: at least as many machines as jobs).
QUESTION: is there a schedule of length (makespan) at most `6`? A schedule assigns every job a
machine and a unit time slot; each machine handles at most one job at a time; and for every arc
`j → k` of `G`, job `k` cannot start before `j` has completed, plus a communication delay of one
time unit when `j` and `k` are processed on different machines (no delay on the same machine).

This is `P̄|prec,c=1,p_j=1|C_max ≤ 6` (`P∞|prec,p_j=1,c_jk=1|C_max ≤ 6`). Hoogeveen, Lenstra and
Veltman distinguish the variant with a restrictively small number of machines
(`P|prec,c=1,p_j=1|C_max`) from the variant `P̄` where it is not restrictive, and prove that for
`P̄` deciding whether an instance has a schedule of length at most 6 is NP-complete, while length
at most 5 is decidable in polynomial time.

It restricts UET-UCT SCHEDULING (`UetUctSchedulingWanted`), whose instance type, schedule and
question are reused unchanged: machine count `m`, the jobs' unit processing times (one entry
per job, so `n` is the length of that list), arc list and bound `d`
(`UetUctScheduling.UetUctSchedulingInstance`), the parent's well-formedness
(`UetUctScheduling.WellFormed`: `0 < m`, unit processing times, arcs name jobs, acyclic
precedence graph) and question
(`UetUctScheduling.UetUctSchedulingFeasible`). The restriction adds `n ≤ m` and `d = 6`. With at
least as many machines as jobs the number of machines never binds: any schedule can be
relabelled to use at most `n` machines, one per job, and every job may have a machine of its own,
which is the source's unrestricted variant.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed UET-UCT SCHEDULING instance with at least as
many machines as jobs (`n ≤ m`, so the number of machines is not restrictive) and bound
`d = 6`. -/
def WellFormed (i : UetUctSchedulingInstance) : Prop :=
  UetUctScheduling.WellFormed i ∧ i.2.1.length ≤ i.1 ∧ i.2.2.2 = 6

open Classical in
/-- UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6 as a decision
problem over bitstrings. -/
noncomputable def uetUctUnboundedMakespanSixDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := UetUctSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ UetUctScheduling.UetUctSchedulingFeasible i)
  | none => false

/-- **UET-UCT SCHEDULING ON UNBOUNDEDLY MANY PROCESSORS WITH MAKESPAN AT MOST 6 is
NP-complete.** Source: Hoogeveen, Lenstra and Veltman (1994). -/
public theorem_wanted uetUctUnboundedMakespanSix_npComplete :
    uetUctUnboundedMakespanSixDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L uetUctUnboundedMakespanSixDec

end MetaMathlibExt.Complexity.NPComplete.UetUctUnboundedMakespanSix
