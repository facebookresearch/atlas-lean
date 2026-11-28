/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IN-TREE TIME LAGS WITH RELEASE DATES (1|intree(l); pᵢ = 1; rᵢ|C_max) is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Single machine problems with
non-negative time-lags", which lists `1|intree(l); pᵢ = 1; rᵢ|C_max` as strongly NP-hard with
the attribution to Brucker and Knust (1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InTreeTimeLagReleaseMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InTreeTimeLagReleaseMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# IN-TREE TIME LAGS WITH RELEASE DATES (1|intree(l); pᵢ = 1; rᵢ|C_max) is NP-complete

INSTANCE: jobs `1, …, n`, each with processing time `pᵢ = 1` and a release date `rᵢ ∈ ℤ₀⁺`, to
be processed on a single machine that processes at most one job at a time; a precedence
relation `→` on the jobs that is an in-tree (each job has at most one immediate successor); a
time lag `l ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule with start times
`Sᵢ ≥ rᵢ` and completion times `Cᵢ = Sᵢ + 1` such that `i → j` implies `Cᵢ + l ≤ Sⱼ` and the
makespan `max_i Cᵢ` is at most `K`?

Following Brucker and Knust, non-negative finish-start time lags `l_ij` "mean that
`Cᵢ + l_ij ≤ Sⱼ` has to be satisfied for certain pairs `(i, j)` of jobs"; relations with a
special structure are written `intree(l_ij)`, `outtree(l_ij)`, and so on, and "if all time-lags
`l_ij` are equal to a constant `l` which is part of the input, we write `prec(l)`". The
precedence relation is given by the list of its pairs `(i, j)` with `i → j`, required to be a
strict partial order (Mathlib's `IsStrictOrder`); with a common lag `l ≥ 0` and unit processing
times, the lag constraints for the pairs of an acyclic relation and for the pairs of its
transitive closure are satisfied by the same schedules, so giving the closure loses nothing.
`i` is an immediate predecessor of `j` (and `j` an immediate successor of `i`) when `i → j` and
no job `c` has `i → c → j`. Schedules are one-processor schedules in Garey and Johnson's sense
([SS1], reused from `SequencingToMinimizeWeightedTardinessDefs` as `IsOneProcessorSchedule`:
one-to-one start times `σ : J → ℤ₀⁺` such that a job starting later starts no earlier than the
completion of the other). With integer data and unit processing times, integer start times lose
no generality. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **`1|intree(l); pᵢ = 1; rᵢ|C_max` is NP-complete.** Source: Brucker and Knust (1999);
Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted inTreeTimeLagReleaseMakespan_npComplete :
    inTreeTimeLagReleaseMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inTreeTimeLagReleaseMakespanDec

end MetaMathlibExt.Complexity.NPComplete.InTreeTimeLagReleaseMakespan
