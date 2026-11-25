/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH PRECEDENCE TIME LAGS (1|prec(l); pᵢ = 1|C_max) is NP-complete

Source:
J. Y.-T. Leung, O. Vornberger, and J. D. Witthoff, "On some variants of the bandwidth
minimization problem", SIAM Journal on Computing 13 (1984), 650-667, doi:10.1137/0213040
(the directed separation problem is NP-complete for arbitrary `k`, with reductions to
scheduling problems);
V. G. Timkovsky, "Identical parallel machines vs. unit-time shops and preemptions vs. chains in
scheduling complexity", European Journal of Operational Research 149 (2003), 355-376,
doi:10.1016/S0377-2217(02)00767-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Single machine problems with
non-negative time-lags", which lists `1|prec(l); pᵢ = 1|C_max` as strongly NP-hard with these
two references.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceTimeLagMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# SINGLE-MACHINE SCHEDULING WITH PRECEDENCE TIME LAGS (1|prec(l); pᵢ = 1|C_max) is NP-complete

INSTANCE: jobs `1, …, n`, each with processing time `pᵢ = 1`, to be processed on a single
machine that processes at most one job at a time; a precedence relation `→` on the jobs; a
time lag `l ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a schedule with start times
`Sᵢ` and completion times `Cᵢ = Sᵢ + 1` such that `i → j` implies `Cᵢ + l ≤ Sⱼ` and the
makespan `max_i Cᵢ` is at most `K`?

Following Brucker and Knust, non-negative finish-start time lags `l_ij` "mean that
`Cᵢ + l_ij ≤ Sⱼ` has to be satisfied for certain pairs `(i, j)` of jobs"; general relations
are denoted `prec(l_ij)`, and "if all time-lags `l_ij` are equal to a constant `l` which is part
of the input, we write `prec(l)`". The precedence relation is given by the list of its pairs
`(i, j)` with `i → j`, required to be a strict partial order (Mathlib's `IsStrictOrder`); with
a common lag `l ≥ 0` and unit processing times, the lag constraints for the pairs of an acyclic
relation and for the pairs of its transitive closure are satisfied by the same schedules, so
giving the closure loses nothing. Schedules are one-processor schedules in Garey and Johnson's
sense ([SS1], reused from `SequencingToMinimizeWeightedTardinessWanted` as
`IsOneProcessorSchedule`: one-to-one start times `σ : J → ℤ₀⁺` such that a job starting later
starts no earlier than the completion of the other). With integer lags and unit processing
times, integer start times lose no generality. The jobs are listed explicitly, one processing
time per job, each required to be `1` (the convention of `PrecedenceConstrainedSchedulingWanted`
and `ChainsTimeLagsUnitMakespanWanted`, which list unit lengths), so the input length grows with
the number of jobs. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the processing times `[p_1, …, p_n]` of the jobs (all `1`), the pairs `(i, j)`
with `i → j`, the time lag `l` and the bound `K`. -/
abbrev PrecedenceTimeLagMakespanInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed jobs. -/
abbrev Job (i : PrecedenceTimeLagMakespanInstance) : Type := Fin i.1.length

/-- The precedence relation: `j → j'` when the pair `(j, j')` is listed. -/
def Prec (i : PrecedenceTimeLagMakespanInstance) (j j' : Job i) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: every processing time is `1`, every listed pair names two
jobs, and the listed pairs form a strict partial order. -/
def WellFormed (i : PrecedenceTimeLagMakespanInstance) : Prop :=
  (∀ p ∈ i.1, p = 1) ∧ (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Job i) (Prec i)

/-- Some one-processor schedule `σ` of the unit-time jobs (start times `σ j`, completion
times `σ j + 1`) satisfies every time lag (`j → j'` implies `σ j + 1 + l ≤ σ j'`) and has
makespan at most `K`. -/
def PrecedenceTimeLagMakespanFeasible (i : PrecedenceTimeLagMakespanInstance) : Prop :=
  ∃ σ : Job i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ j j', Prec i j j' → σ j + 1 + i.2.2.1 ≤ σ j') ∧ ∀ j, σ j + 1 ≤ i.2.2.2

open Classical in
/-- `1|prec(l); pᵢ = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def precedenceTimeLagMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceTimeLagMakespanInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceTimeLagMakespanFeasible i)
  | none => false

/-- **`1|prec(l); pᵢ = 1|C_max` is NP-complete.** Source: Leung, Vornberger, and Witthoff
(1984); Timkovsky (2003); Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted precedenceTimeLagMakespan_npComplete :
    precedenceTimeLagMakespanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L precedenceTimeLagMakespanDec

end MetaMathlibExt.Complexity.NPComplete.PrecedenceTimeLagMakespan
