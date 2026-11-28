/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O|p_ij=1;outtree|Lmax is NP-complete

Source:
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `o_nop` (open shop problems without
preemption), entry `O|p_ij=1;outtree|L_max` (minimal NP-hard in the strong sense, citing
Timkovsky 2003);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1 (not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness

open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopOutTreeMaxLateness
  (UnitFlowShopOutTreeMaxLatenessInstance WellFormed toInt)
open MetaMathlibExt.Complexity.NPComplete.UnitFlowShopPrecedenceMakespan (Prec)

/-!
# OPEN SHOP O|p_ij=1;outtree|Lmax is NP-complete

INSTANCE: `m ≥ 1` machines `M_1, …, M_m` in an open shop; jobs `1, …, n`, each consisting of `m`
operations `O_j1, …, O_jm` of unit length, `O_jk` processed on `M_k`, in any order but no two of
them at the same time; each machine processes one operation at a time; an out-tree precedence
relation on the jobs (out-forest: each job has at most one immediate predecessor), where `i`
preceding `j` means that no operation of `j` starts before every operation of `i` is completed;
an integer due date `d_j` for each job `j`; and an integer bound `K`. QUESTION: is there a schedule
whose maximum lateness `max_j (C_j - d_j)` is at most `K`, where `C_j` is the completion time of
job `j` (of its last operation)?

This is Brucker and Knust's `O|p_ij=1;outtree|L_max`, which they classify as strongly NP-hard,
citing Timkovsky (2003), whose paper was not available. It differs from the flow shop
`F|p_ij=1;outtree|L_max` (`UnitFlowShopOutTreeMaxLatenessWanted`) only in the machine order of a
job's operations, which is free here. The instance type (each job listed with its processing
times, all `1`, and its due date; precedence arcs; integers as pairs `(a, b)` standing for
`a - b`), the well-formedness (`m ≥ 1`, unit jobs, acyclic arcs naming jobs, each job with at most
one immediate predecessor in the generated order) and `toInt` are reused from that module, and
`Prec` from `UnitFlowShopPrecedenceMakespanWanted`. A schedule gives each operation `O_jk` a
start time `σ k j ∈ ℕ` (integer start times suffice for unit operations); the operations on one
machine, and the operations of one job, start at pairwise different times, i.e. do not overlap
(`IsUnitOpenShopSchedule`). Numbers use the binary encoding. Membership in NP is the certificate
argument: the `n · m` start times (each below `d_j + K` for its job `j`) are checked in polynomial
time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPEN SHOP O|p_ij=1;outtree|Lmax is NP-complete.** Source: Brucker and Knust's
classification (strongly NP-hard), citing Timkovsky (2003). -/
public theorem_wanted unitOpenShopOutTreeMaxLateness_npComplete :
    unitOpenShopOutTreeMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopOutTreeMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopOutTreeMaxLateness
