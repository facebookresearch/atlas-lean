/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS (decision version);
D. Bernstein, M. Rodeh and I. Gertner, "Approximation algorithms for scheduling arithmetic
expressions on pipelined machines", J. Algorithms 10 (1989), 120-139,
doi:10.1016/0196-6774(89)90027-8 (the problem);
J. Y.-T. Leung, O. Vornberger and J. D. Witthoff, "On some variants of the bandwidth
minimization problem", SIAM J. Comput. 13 (1984), 650-667, doi:10.1137/0213040 (the case of
equal delays, `1|prec(l); pᵢ = 1|C_max`, recorded as strongly NP-hard by P. Brucker and
S. Knust, *Complexity results for scheduling problems*, class "Single machine problems with
non-negative time-lags").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PrecedenceConstrainedSequencingWithDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSequencingWithDelays

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS is NP-complete

INSTANCE: a set `T` of tasks, a directed acyclic graph `G = (T, E)` defining precedence
constraints for the tasks, a positive integer `D`, for each task an integer delay
`0 ≤ d(t) ≤ D`, and a positive integer `K`.
QUESTION: is there a one-processor schedule for `T` that obeys the precedence constraints and
the delays, that is, an injective function `S : T → ℤ⁺` such that `S(tⱼ) - S(tᵢ) > d(tᵢ)` for
each edge `⟨tᵢ, tⱼ⟩ ∈ E`, with finish time `max_{t ∈ T} S(t) ≤ K`?

The tasks are `0, ..., n - 1`, one listed delay per task, and the edges are listed pairs
`(i, j)`, required to form an acyclic relation (no task reaches itself along edges). Start times
are written `S(t) = σ(t) + 1` with `σ : T → ℕ`; injectivity of `S` is the one-processor
condition for unit-time tasks (`IsOneProcessorSchedule` with all lengths `1`, reused from
`SequencingToMinimizeWeightedTardinessDefs`), the delay constraint reads
`σ(tᵢ) + d(tᵢ) < σ(tⱼ)`, and the finish time bound reads `σ(t) + 1 ≤ K`. With all delays equal
to one value `l` the problem is `1|prec(l); pᵢ = 1|C_max`
(`PrecedenceTimeLagMakespanWanted`), which gives NP-hardness. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS is NP-complete.** Source: Crescenzi and
Kann, MINIMUM PRECEDENCE CONSTRAINED SEQUENCING WITH DELAYS; Bernstein, Rodeh and Gertner (1989);
Leung, Vornberger and Witthoff (1984) for equal delays. -/
public theorem_wanted precedenceConstrainedSequencingWithDelays_npComplete :
    precedenceConstrainedSequencingWithDelaysDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceConstrainedSequencingWithDelaysDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceConstrainedSequencingWithDelays
