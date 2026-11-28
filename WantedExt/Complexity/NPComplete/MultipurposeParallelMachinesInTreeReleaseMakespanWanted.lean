/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM PARALLEL MACHINES `PMPM|intree; p_i = 1; r_i|C_max` is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `mpm` (multi-purpose machine
problems), entry `PMPM|intree; p_i = 1; r_i|C_max` (minimal NP-hard in the strong sense, citing
Brucker, Garey and Johnson 1977);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5,
Chapter 10 (multi-purpose machines).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipurposeParallelMachinesInTreeReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesInTreeReleaseMakespan

open PrecedenceConstrainedScheduling (Task taskLength Prec)
open ParallelMachinesInTreeReleaseMakespan (ParallelMachinesInTreeReleaseMakespanInstance
  releaseDate)

/-!
# MPM PARALLEL MACHINES `PMPM|intree; p_i = 1; r_i|C_max` is NP-complete

INSTANCE: identical parallel machines `M_1, …, M_m` (`m ≥ 1` part of the input); jobs
`1, …, n`, each with processing time `p_i = 1`, a release date `r_i ∈ ℤ₀⁺` and a nonempty set
`μ_i ⊆ {M_1, …, M_m}` of eligible machines; an in-tree precedence relation `→` on the jobs (no
job has more than one immediate successor); and a bound `K`. QUESTION: is there a feasible
schedule with makespan `max_i C_i ≤ K`? In a feasible schedule each job is processed on exactly
one machine of `μ_i`, each machine processes at most one job at a time, job `i` starts no
earlier than `r_i`, and `i → j` means that `j` cannot start before `i` is completed.

This is Brucker's multi-purpose machine (MPM) model on identical parallel machines (Chapter 10:
a job has to be processed by one machine of its set `μ_i`). With every `μ_i = {M_1, …, M_m}` it
is `P|intree; r_i; p_i = 1|C_max` (`ParallelMachinesInTreeReleaseMakespanWanted`), which is
NP-hard in the strong sense by Brucker, Garey and Johnson (1977) (see that module); Brucker and
Knust record `PMPM|intree; p_i = 1; r_i|C_max` as minimal NP-hard in the strong sense among the
MPM problems, citing Brucker, Garey and Johnson (1977). NP membership: start times and machines
form a certificate of polynomial size in the binary input (each start time is below `K` in a
yes-instance and each machine is a listed entry), checked in polynomial time.

Encoding. The machines, jobs, release dates, precedence relation and bound are a
`P|intree; r_i; p_i = 1|C_max` instance, whose well-formedness is reused (unit processing
times, one per listed job; `m > 0`; the pairs `(t, t')` with `t → t'` in the transitive closure,
a strict order whose Hasse diagram is an in-forest; one release date per job; `K > 0`). The
eligible sets are listed one per job, machines numbered `0, …, m - 1`, each set nonempty. A
schedule gives each job `t` a start time `σ t` and a machine `a t ∈ μ_t`; two different jobs on
the same machine are processed in disjoint intervals. With integer data, integer start times
lose no generality. Binary encoding of all numbers (the problem is NP-hard in the strong
sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MPM PARALLEL MACHINES `PMPM|intree; p_i = 1; r_i|C_max` is NP-complete.** Source:
Brucker, Garey and Johnson (1977); Brucker and Knust, *Complexity results for scheduling
problems*. -/
public theorem_wanted multipurposeParallelMachinesInTreeReleaseMakespan_npComplete :
    multipurposeParallelMachinesInTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipurposeParallelMachinesInTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.MultipurposeParallelMachinesInTreeReleaseMakespan
