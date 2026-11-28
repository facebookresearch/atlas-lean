/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARALLEL MACHINES WITH IN-TREE AND RELEASE DATES (P|intree; r_i; p_i = 1|C_max) is NP-complete

Source:
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2(3)
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Parallel machine problems without
preemption", which lists `P|intree; r_i; p_i = 1|C_max` as minimal NP-hard in the strong sense
with the attribution to Brucker, Garey and Johnson (1977);
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007), Chapter 1 (notation) and
Section 5.2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespan

open PrecedenceConstrainedScheduling (PrecedenceConstrainedSchedulingInstance Task taskLength
  Prec running)
open PrecedenceConstrainedSchedulingOpposingForests (ImmediatePredecessor)

/-!
# PARALLEL MACHINES WITH IN-TREE AND RELEASE DATES (P|intree; r_i; p_i = 1|C_max) is NP-complete

INSTANCE: `m ≥ 1` identical parallel machines; jobs `1, …, n`, each with processing time
`p_i = 1` and a release date `r_i ∈ ℤ₀⁺`; an in-tree precedence relation `→` on the jobs (no job
has more than one immediate successor); and a bound `K`. QUESTION: is there a feasible schedule
with makespan `max_i C_i ≤ K`? In a feasible schedule each machine processes at most one job at
a time, job `i` starts no earlier than `r_i`, and `i → j` means that `j` cannot start before `i`
is completed.

NP-hardness: Brucker, Garey and Johnson (1977) prove that scheduling unit tasks on `m`
processors under an out-tree partial order (no task has more than one immediate predecessor)
to meet individual deadlines is NP-complete (Garey and Johnson, [SS11], comment). Reversing time
(`σ'(t) = K - 1 - σ(t)`, `r_t = K - d_t`) turns that problem into this one, and Brucker and
Knust record `P|intree; r_i; p_i = 1|C_max` as minimal NP-hard in the strong sense with the
attribution to Brucker, Garey and Johnson (1977). NP membership: a schedule is given by integer
start times, each below `K` in a yes-instance, a certificate of polynomial size in the binary
input that is checked in polynomial time.

Encoding. The machine environment, jobs and precedence relation are a PRECEDENCE CONSTRAINED
SCHEDULING instance (`P|prec; p_i = 1|C_max`, Garey and Johnson [SS9],
`PrecedenceConstrainedSchedulingWanted`): the processing times (job `t` is the `t`-th entry, all
`1`, so the jobs are listed one by one), the number `m > 0` of machines, the pairs `(t, t')` with
`t → t'` in the transitive closure, required to form a strict order, and the bound `K` (that
module's deadline `D`, which its well-formedness asks to be positive; with `K = 0` only the
instance without jobs would be a yes-instance). The schedule conditions (`running`: at most `m`
jobs in process at each time; precedence; completion by `K`) are those of that module, plus the
release dates, listed one per job. The in-tree condition says that no job has more than one
immediate successor (`ImmediatePredecessor`, from
`PrecedenceConstrainedSchedulingOpposingForestsWanted`), as in Garey and Johnson's [SS11]
comment and Brucker, Garey and Johnson (1977); a forest of in-trees is allowed. With integer
data, integer start times lose no generality. Binary encoding of all numbers (the problem is
NP-hard in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`P|intree; r_i; p_i = 1|C_max` is NP-complete.** Source: Brucker, Garey and Johnson
(1977); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted parallelMachinesInTreeReleaseMakespan_npComplete :
    parallelMachinesInTreeReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L parallelMachinesInTreeReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.ParallelMachinesInTreeReleaseMakespan
