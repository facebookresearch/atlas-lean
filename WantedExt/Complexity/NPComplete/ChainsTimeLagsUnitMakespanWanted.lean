/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE MAKESPAN with chains, time lags and unit processing times is NP-complete

Source:
W. Yu, H. Hoogeveen and J. K. Lenstra, "Minimizing makespan in a two-machine flow shop with
delays and unit-time operations is NP-hard", Journal of Scheduling 7 (2004), 333-348,
doi:10.1023/B:JOSH.0000036858.59787.c2, Theorem 24;
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (single machine problems with
non-negative time-lags: `1|chains(lᵢⱼ); pᵢ = 1|C_max`, minimal NP-hard in the strong sense,
Yu (1996), Yu et al. (2004)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainsTimeLagsUnitMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsTimeLagsUnitMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SINGLE-MACHINE MAKESPAN with chains, time lags and unit processing times is NP-complete

INSTANCE: jobs `1, …, n` to be processed on a single machine that executes at most one job at a
time, each with processing time `pᵢ = 1`; finish-start time lags on certain pairs `(i, j)` of
jobs, a nonnegative integer `lᵢⱼ` on each pair, requiring `Cᵢ + lᵢⱼ ≤ Sⱼ` for the completion
time `Cᵢ` of `i` and the starting time `Sⱼ` of `j`, where the pairs form chains (each job is the
first job of at most one pair and the second job of at most one pair, and the pairs have no
cycle); and a bound `K`. QUESTION: is there a schedule satisfying all time lags whose makespan
`max Cᵢ` is at most `K`?

This is `1|chains(lᵢⱼ); pᵢ = 1|C_max` in Brucker and Knust's classification. NP-hardness: Yu,
Hoogeveen and Lenstra (2004), Theorem 24, prove that minimizing the makespan on a single
machine with two unit-time operations per job and arbitrary intermediate delays is strongly
NP-hard; that problem is the special case in which every chain consists of exactly two jobs
(the two operations of a job, with the job's delay as the time lag). Membership in NP holds
because start times below `K`, one per listed job, are a certificate of polynomial size.

The jobs are listed explicitly, one processing time per job (so the input length is at least
the number of jobs), and are `Fin n` for `n` listed processing times; `WellFormed` requires
every processing time to be `1`. The pairs are given as a list of triples `(i, j, lᵢⱼ)`; "each
job is the first job of at most one pair and the second job of at most one pair" says that no
job is listed twice as a first component and none twice as a second component, and acyclicity
says that the transitive closure (Mathlib's `Relation.TransGen`) of the pair relation is
irreflexive. A schedule is a one-processor schedule `σ` of start times in the sense of Garey and
Johnson's
[SS1] (`IsOneProcessorSchedule`, reused from `SequencingToMinimizeWeightedTardinessDefs`);
job `i` completes at `Cᵢ = σ(i) + pᵢ = σ(i) + 1`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SINGLE-MACHINE MAKESPAN with chains, time lags and unit processing times is NP-complete.**
Source: Yu, Hoogeveen and Lenstra (2004), Theorem 24 (NP-hardness, chains of two jobs); Yu
(1996). -/
public theorem_wanted chainsTimeLagsUnitMakespan_npComplete :
    chainsTimeLagsUnitMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsTimeLagsUnitMakespanDec

end MetaMathlibExt.Complexity.NPComplete.ChainsTimeLagsUnitMakespan
