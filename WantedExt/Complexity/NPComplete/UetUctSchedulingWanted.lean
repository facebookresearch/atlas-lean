/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UET-UCT SCHEDULING (UNIT COMMUNICATION DELAYS) is NP-complete

Source:
V. J. Rayward-Smith, "UET scheduling with unit interprocessor communication delays", Discrete
Applied Mathematics 18 (1987), 55-71, doi:10.1016/0166-218X(87)90042-4;
J. A. Hoogeveen, J. K. Lenstra, and B. Veltman, "Three, four, five, six, or the complexity of
scheduling with communication delays", Operations Research Letters 16 (1994), 129-137,
doi:10.1016/0167-6377(94)90024-8, Theorem 2 (NP-complete already for the bound `4`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS9] PRECEDENCE CONSTRAINED
SCHEDULING (the problem without communication delays).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UetUctSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UetUctScheduling

/-!
# UET-UCT SCHEDULING (UNIT COMMUNICATION DELAYS) is NP-complete

INSTANCE: `m` identical parallel processors, `n` tasks with unit processing times, an acyclic
directed graph `G` on the tasks (an arc `j → k` whenever task `k` needs data from task `j`),
and a bound `d`. QUESTION: is there a schedule of length (makespan) at most `d`, i.e. an
allocation of each task to a time slot of unit length on a processor such that each processor
executes at most one task at a time, and for every arc `j → k` task `k` starts no earlier than
the completion of `j`, plus a communication delay of one time unit when `j` and `k` are
executed on different processors?

This is `P|prec,c=1,p_j=1|C_max` with `m` part of the input, as defined by Hoogeveen, Lenstra
and Veltman (1994): with start times `S_j` and completion times `C_j = S_j + 1`, an arc
`j → k` requires `S_k ≥ C_j` if `j` and `k` share a processor and `S_k ≥ C_j + 1` otherwise,
and the makespan is `max_j C_j`. Rayward-Smith (1987) established NP-hardness; Hoogeveen,
Lenstra and Veltman prove the question NP-complete already for `d = 4`. The constraint is
imposed on the arcs of `G`; on the rest of its transitive closure it follows, since every
task has unit length (a path `j → k → k'` already gives `S_k' ≥ C_j + 1`). Processors are
`Fin m`, tasks `Fin n`. The tasks are listed explicitly, one processing time per task, each
required to be `1` (the convention of `PrecedenceConstrainedSchedulingWanted`, which lists unit
task lengths), so the input length grows with the number of tasks. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UET-UCT SCHEDULING (UNIT COMMUNICATION DELAYS) is NP-complete.** Source: Rayward-Smith
(1987); Hoogeveen, Lenstra, and Veltman (1994), Theorem 2. -/
public theorem_wanted uetUctScheduling_npComplete :
    uetUctSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L uetUctSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.UetUctScheduling
