/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR-TASK SCHEDULING `P2|chains;p_i=1;size_i|L_max` is NP-complete

Source:
P. Brucker, S. Knust, D. Roper and Y. Zinder, "Scheduling UET task systems with concurrency
on two parallel identical processors", Mathematical Methods of Operations Research 52 (2000),
369-387, doi:10.1007/s001860000089;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with parallel processors" (`P2|chains;p_i=1;size_i|L_max`,
minimal NP-hard in the strong sense, citing Brucker et al. 2000; the class page defines the
model: each task `i` requires `size_i` of the `m` identical processors during its processing).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitSizeChainsMaxLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitSizeChainsMaxLateness

open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)

/-!
# MULTIPROCESSOR-TASK SCHEDULING `P2|chains;p_i=1;size_i|L_max` is NP-complete

INSTANCE: `m = 2` identical parallel processors, each processing at most one task at a time;
tasks `1, …, n`, each with unit processing time `p_i = 1` and a size `size_i ∈ {1, 2}`: task `i`
requires `size_i` processors simultaneously during its processing, and any `size_i` processors
may be used; a precedence relation on the tasks consisting of chains (every task has at most one
immediate predecessor and at most one immediate successor): if `i` precedes `j`, then `j` cannot
start before `i` is completed; an integer due date `d_i` for each task `i`; and an integer bound
`K`. QUESTION: is there a feasible schedule whose maximum lateness `max_i (C_i - d_i)` is at most
`K`, where `C_i` is the completion time of task `i`?

The tasks are `Fin n`, listed by their sizes and due dates. A schedule gives each task a start
time `S i`; with unit tasks, the tasks running during `[u, u + 1)` are those with `S i = u`, and
since the processors are identical and any `size_i` of them may be used, a set of unit tasks can
run in one time slot exactly when their sizes sum to at most `2`. The chains are given by their
arcs `(i, j)` (task `i` immediately precedes task `j`), with the chain conditions of
`F3UnitChainsLateJobs.ChainsWellFormed` (distinct arcs naming tasks, no task with two immediate
successors or two immediate predecessors, no cycle); an arc requires `S i + 1 ≤ S j`, and the
whole precedence relation follows by transitivity. The bound is stated as `C_i - d_i ≤ K` for
every task `i`, with `C_i = S i + 1`; there is at least one task, since `max_i (C_i - d_i)` is
undefined for an empty task set. Due dates and `K` are integers given as
`(positive part, negative part)` pairs. Integral start times lose no generality for unit tasks.
Binary encoding of all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPROCESSOR-TASK SCHEDULING `P2|chains;p_i=1;size_i|L_max` is NP-complete.** Source:
Brucker, Knust, Roper and Zinder (2000), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoProcessorUnitSizeChainsMaxLateness_npComplete :
    twoProcessorUnitSizeChainsMaxLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitSizeChainsMaxLatenessDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitSizeChainsMaxLateness
