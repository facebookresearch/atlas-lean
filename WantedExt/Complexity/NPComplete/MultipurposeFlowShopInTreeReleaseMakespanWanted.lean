/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, IN-TREE, RELEASE DATES (FMPM|intree; r_i; p_ij = 1|C_max) is NP-complete

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Sections 1.2, 1.3 and 5.2
(release dates, precedence relations, in-trees), Chapter 10 (the MPM flow-shop model) and Table 5.3
(`P|p_i = 1; intree; r_i|C_max` is NP-hard, Brucker, Garey and Johnson);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|intree; r_i; p_ij = 1|C_max` as strongly NP-hard with the
attribution to Brucker, Garey and Johnson (1977).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed Prec PrecedenceWellFormed
  IsPrecedenceSchedule completionTime)

/-!
# MPM FLOW SHOP, IN-TREE, RELEASE DATES (FMPM|intree; r_i; p_ij = 1|C_max) is NP-complete

INSTANCE: machines `M_1, …, M_m`; an MPM flow shop with `r ≥ 1` stages and machine sets
`μ_1, …, μ_r ⊆ {M_1, …, M_m}`, pairwise different; jobs `J_1, …, J_n`, each consisting of `r`
operations `O_i1, …, O_ir` with processing times `p_ij = 1` and with a release date `r_i ∈ ℤ₀⁺`;
a precedence relation `→` on the jobs that is an in-tree (each job has at most one immediate
successor); and a bound `K`. QUESTION: is there a feasible schedule in which no job starts
before its release date and the makespan `max_i C_i` is at most `K`?

The MPM flow-shop model, its schedules and precedence constraints are those of
`FMPM|prec; p_ij = 1|C_max`
(`WantedExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanWanted`, which states
Brucker's model: `StagesWellFormed`, `Prec`, `PrecedenceWellFormed`, `IsPrecedenceSchedule`,
`completionTime`, reused here). In-trees follow Brucker (Section 5.2): "intrees (outtrees) which
are precedence constraints with the property that each `IS(i)` (`IP(i)`) contains at the most
one job", where `IS(i)` is the set of immediate successors of `i`. The precedence relation is
given by the list of its pairs, required to be a strict partial order; `k` is an immediate
successor of `i` when `i → k` and no job `c` has `i → c → k`. Release dates follow Brucker
(Section 1.2: "a release date `r_i`, on which the first operation of `J_i` becomes available for
processing"); no operation of job `i` starts before `r_i`, which by the stage order is the same
as its first operation not starting before `r_i`. The jobs are `Fin n` for `n` listed release
dates. Every stage machine set must be nonempty: an operation "has to be processed by one
machine in the set" (Brucker, Chapter 10). Binary encoding of all numbers (the problem is
NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`FMPM|intree; r_i; p_ij = 1|C_max` is NP-complete.** Source: Brucker (2007), Chapter 10
and Table 5.3; Brucker, Garey and Johnson (1977); Brucker and Knust, *Complexity results for
scheduling problems*. -/
public theorem_wanted multipurposeFlowShopInTreeReleaseMakespan_npComplete :
    multipurposeFlowShopInTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeFlowShopInTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespan
