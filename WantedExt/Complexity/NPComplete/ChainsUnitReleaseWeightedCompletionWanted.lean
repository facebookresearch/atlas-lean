/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE WEIGHTED COMPLETION TIME with chains, unit processing times and release dates
# is NP-complete

Source:
J. K. Lenstra and A. H. G. Rinnooy Kan, "Complexity results for scheduling chains on a single
machine", European Journal of Operational Research 4 (1980), 270-275,
doi:10.1016/0377-2217(80)90111-3, Theorem 3 (`1|chain, rⱼ, pⱼ = 1|∑ wⱼCⱼ`);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/ (single machine problems:
`1|chains; pᵢ = 1; rᵢ|∑ wᵢCᵢ`, minimal NP-hard in the strong sense, Lenstra and Rinnooy Kan
(1980)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ChainsUnitReleaseWeightedCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitReleaseWeightedCompletion

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SINGLE-MACHINE WEIGHTED COMPLETION TIME with chains, unit processing times and release dates
# is NP-complete

INSTANCE: jobs `J₁, …, Jₙ` to be processed on a single machine that executes at most one job at
a time, each requiring one unit of uninterrupted processing time (`pⱼ = 1`) and having a release
date `rⱼ` (a lower bound on its starting time) and a weight `wⱼ`; a precedence relation `→`
derived from an acyclic directed graph on the jobs (`Jⱼ → Jₖ` when there is a directed path from
`Jⱼ` to `Jₖ`) that is chain-like (each vertex has indegree at most one and outdegree at most
one); and a bound `K`. QUESTION: is there a schedule respecting the release dates and the
precedence relation (`Jⱼ → Jₖ` requires `Jⱼ` to be completed before `Jₖ` can start) whose total
weighted completion time `∑ⱼ wⱼCⱼ` is at most `K`?

This is `1|chain, rⱼ, pⱼ = 1|∑ wⱼCⱼ`, Theorem 3 of Lenstra and Rinnooy Kan (1980), who state
the scheduling model, the precedence relation and the chain condition as above (their
Section 1 and Figure 1(d)) and prove NP-hardness. Membership in NP holds because a schedule is a
certificate of polynomial size: some schedule of minimum `∑ wⱼCⱼ` starts every job before
`max rⱼ + n`.

The jobs are `Fin n`, one per listed pair `(rⱼ, wⱼ)`; release dates and weights are nonnegative
integers (the chain construction in Lenstra and Rinnooy Kan's proof of their Theorem 2, which
their Theorem 3 reuses, gives weight `0` to all but the last job of a chain). The directed graph
is given by its list of arcs `(j, k)`; indegree and outdegree at most one say that no job is
listed twice as the head of an arc and no job is listed twice as its tail, and acyclicity says
that the transitive closure (Mathlib's `Relation.TransGen`) of the arc relation is irreflexive.
A schedule is a one-processor schedule `σ` of start times in the sense of Garey and Johnson's
[SS1], with every length `1` (`IsOneProcessorSchedule`, reused from
`SequencingToMinimizeWeightedTardinessDefs`); job `Jⱼ` completes at `Cⱼ = σ(j) + 1`. Binary
encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SINGLE-MACHINE WEIGHTED COMPLETION TIME with chains, unit processing times and release
dates is NP-complete.** Source: Lenstra and Rinnooy Kan (1980), Theorem 3 (NP-hardness). -/
public theorem_wanted chainsUnitReleaseWeightedCompletion_npComplete :
    chainsUnitReleaseWeightedCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chainsUnitReleaseWeightedCompletionDec

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitReleaseWeightedCompletion
