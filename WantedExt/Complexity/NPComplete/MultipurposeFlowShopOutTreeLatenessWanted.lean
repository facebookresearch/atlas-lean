/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, OUT-TREE, MAXIMUM LATENESS (FMPM|outtree; p_ij = 1|L_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Sections 1.2, 1.3, 1.5 and 5.2
(due dates, precedence relations, lateness, out-trees), Chapter 10 (the MPM flow-shop model) and
Table 5.3 (`P|p_i = 1; outtree|L_max` is NP-hard, Brucker, Garey and Johnson);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|outtree; p_ij = 1|L_max` as strongly NP-hard with the attribution
to Brucker, Garey and Johnson (1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLateness

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed Prec PrecedenceWellFormed
  IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP, OUT-TREE, MAXIMUM LATENESS (FMPM|outtree; p_ij = 1|L_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1` and with a due date `d_i ∈ ℤ`; a
precedence relation `→` on the jobs that is an out-tree (each job has at most one immediate
predecessor); and a bound `K ∈ ℤ`. QUESTION: is there a feasible schedule in which the maximum
lateness `max_i (C_i - d_i)` is at most `K`?

The MPM flow-shop model, its schedules and precedence constraints are those of
`FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's model: `StagesWellFormed`, `Prec`, `PrecedenceWellFormed`, `IsPrecedenceSchedule`,
`completionTime`, reused here). Out-trees follow Brucker (Section 5.2): "intrees (outtrees) which
are precedence constraints with the property that each `IS(i)` (`IP(i)`) contains at the most
one job", where `IP(i)` is the set of immediate predecessors of `i`. The precedence relation is
given by the list of its pairs, required to be a strict partial order; `j` is an immediate
predecessor of `k` when `j → k` and no job `c` has `j → c → k`. The lateness of job `i` is
`C_i - d_i` (Brucker, Section 1.5: "`L_i := C_i − d_i` lateness"; `L_max` is the maximum
lateness). The due dates and the bound are integers, each encoded as a pair of naturals
`(positive part, negative part)` as in `ZeroOneILPWanted`; `L_max ≤ K` is stated as
`C_i - d_i ≤ K` for every job `i`; `WellFormed` requires `n ≥ 1`, since a maximum over no jobs
is undefined. The jobs are `Fin n` for `n` listed due dates. Binary encoding of all numbers (the
problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`FMPM|outtree; p_ij = 1|L_max` is NP-complete.** Source: Brucker (2007), Chapter 10 and
Table 5.3; Brucker, Garey and Johnson (1977); Brucker and Knust, *Complexity results for
scheduling problems*. -/
public theorem_wanted multipurposeFlowShopOutTreeLateness_npComplete :
    multipurposeFlowShopOutTreeLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopOutTreeLatenessDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopOutTreeLateness
