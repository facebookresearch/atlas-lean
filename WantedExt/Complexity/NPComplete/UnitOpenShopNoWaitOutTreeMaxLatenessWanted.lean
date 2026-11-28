/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*, classification tables
(class "Open-shop problems with no-wait", minimal NP-hard entry
`O | p_ij = 1; outtree; no-wait | L_max`, NP-hard in the strong sense, credited to Brucker, Garey
and Johnson (1977));
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopNoWaitOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitOutTreeMaxLateness

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness
  (UnitFlowShopOutTreeMaxLatenessInstance WellFormed toInt)
open MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness (IsUnitOpenShopSchedule)

/-!
# NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax is NP-complete

INSTANCE: a number `m ≥ 1` of machines `M_1, …, M_m` in an open shop, `n` jobs, each job `j`
consisting of `m` operations `O_j1, …, O_jm` with processing times `p_jk = 1`, where `O_jk` is
processed on `M_k` and the operations of a job may be processed in any order, but no two of them
at the same time; an out-tree precedence relation on the jobs (out-forest: each job has at most
one immediate predecessor; if `i` precedes `j`, then no operation of `j` starts before every
operation of `i` is completed); an integer due date `d_j` for each job `j`; and an integer bound
`K`. Each machine processes at most one operation at a time, and no job waits: there is no
waiting time between consecutive operations of a job. QUESTION: is there a schedule whose maximum
lateness `max_j (C_j - d_j)` is at most `K`, where `C_j` is the completion time of job `j` (of
its last operation)?

The instance and its well-formedness are those of the unit-time flow shop with out-tree
precedence and due dates (`UnitFlowShopOutTreeMaxLatenessWanted`: `m ≥ 1`, each job listed with
its `m` unit processing times and its due date, acyclic precedence arcs generating an out-tree
relation, integers as pairs `(a, b)` standing for `a - b`); the schedule is the open-shop
schedule `IsUnitOpenShopSchedule` of `UnitOpenShopOutTreeMaxLatenessWanted` (integer start times
`σ k j` of operation `O_jk`). A job's `m` unit operations start at distinct integer times, so the
job waits between none of them exactly when they occupy the `m` consecutive unit slots starting at
some time `s`: `s ≤ σ k j < s + m` for every machine `k`. Numbers use the binary encoding.

Brucker and Knust classify the problem as NP-hard in the strong sense, crediting Brucker, Garey
and Johnson, who prove the parallel-machine problem with unit-time jobs, out-tree precedence
constraints and maximum lateness NP-hard. Membership in NP is the certificate argument: the
`n · m` start times of a schedule (each below `d_j + K` for its job `j`) are checked in
polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NO-WAIT OPEN SHOP O|p_ij=1;outtree;no-wait|Lmax is NP-complete.** Source: Brucker and
Knust's classification (strongly NP-hard), citing Brucker, Garey and Johnson (1977); membership
in NP is the certificate argument in the module docstring. -/
public theorem_wanted unitOpenShopNoWaitOutTreeMaxLateness_npComplete :
    unitOpenShopNoWaitOutTreeMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopNoWaitOutTreeMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopNoWaitOutTreeMaxLateness
