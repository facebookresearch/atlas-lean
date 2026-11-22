/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OUT-TREE TIME LAGS, MAXIMUM LATENESS (1|outtree(l); pᵢ = 1|L_max) is NP-complete

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Single machine problems with
non-negative time-lags", which lists `1|outtree(l); pᵢ = 1|L_max` as strongly NP-hard with the
attribution to Brucker and Knust (1999).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import WantedExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OutTreeTimeLagLateness

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-!
# OUT-TREE TIME LAGS, MAXIMUM LATENESS (1|outtree(l); pᵢ = 1|L_max) is NP-complete

INSTANCE: jobs `1, …, n`, each with processing time `pᵢ = 1` and a due date `dᵢ ∈ ℤ`, to be
processed on a single machine that processes at most one job at a time; a precedence relation
`→` on the jobs that is an out-tree (each job has at most one immediate predecessor); a time
lag `l ∈ ℤ₀⁺`; and a bound `K ∈ ℤ`. QUESTION: is there a schedule with start times `Sᵢ` and
completion times `Cᵢ = Sᵢ + 1` such that `i → j` implies `Cᵢ + l ≤ Sⱼ` and the maximum
lateness `max_i (Cᵢ - dᵢ)` is at most `K`?

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
([SS1], reused from `SequencingToMinimizeWeightedTardinessWanted` as `IsOneProcessorSchedule`:
one-to-one start times `σ : J → ℤ₀⁺` such that a job starting later starts no earlier than the
completion of the other). With integer data and unit processing times, integer start times lose
no generality. The due dates and the bound are integers, each encoded as a
pair of naturals `(positive part, negative part)` as in `ZeroOneILPWanted`; `L_max ≤ K` is
stated as `Cᵢ - dᵢ ≤ K` for every job `i`. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the due dates `d₀, …, dₙ₋₁` as `(positive part, negative part)` pairs, the
pairs `(i, j)` with `i → j`, the time lag `l`, and the bound `K` as a `(positive part,
negative part)` pair. -/
abbrev OutTreeTimeLagLatenessInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` due dates. -/
abbrev Job (i : OutTreeTimeLagLatenessInstance) : Type := Fin i.1.length

/-- The due date `dⱼ ∈ ℤ` of job `j`. -/
def dueDate (i : OutTreeTimeLagLatenessInstance) (j : Job i) : ℤ :=
  ((i.1.get j).1 : ℤ) - ((i.1.get j).2 : ℤ)

/-- The bound `K ∈ ℤ` on the maximum lateness. -/
def bound (i : OutTreeTimeLagLatenessInstance) : ℤ :=
  (i.2.2.2.1 : ℤ) - (i.2.2.2.2 : ℤ)

/-- The precedence relation: `j → j'` when the pair `(j, j')` is listed. -/
def Prec (i : OutTreeTimeLagLatenessInstance) (j j' : Job i) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2.1

/-- `j` is an immediate predecessor of `j'`: `j → j'`, and no job `c` has `j → c → j'`. -/
def ImmediatePredecessor (i : OutTreeTimeLagLatenessInstance) (j j' : Job i) : Prop :=
  Prec i j j' ∧ ∀ c, ¬ (Prec i j c ∧ Prec i c j')

/-- Well-formedness of an instance: every listed pair names two jobs, the listed pairs form a
strict partial order, and the order is an out-tree (every job has at most one immediate
predecessor). -/
def WellFormed (i : OutTreeTimeLagLatenessInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Job i) (Prec i) ∧
    ∀ j a b, ImmediatePredecessor i a j → ImmediatePredecessor i b j → a = b

/-- Some one-processor schedule `σ` of the unit-time jobs (start times `σ j`, completion
times `σ j + 1`) satisfies every time lag (`j → j'` implies `σ j + 1 + l ≤ σ j'`) and has
maximum lateness at most `K`: `(σ j + 1) - dⱼ ≤ K` for every job `j`. -/
def OutTreeTimeLagLatenessFeasible (i : OutTreeTimeLagLatenessInstance) : Prop :=
  ∃ σ : Job i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ j j', Prec i j j' → σ j + 1 + i.2.2.1 ≤ σ j') ∧
    ∀ j, ((σ j + 1 : ℕ) : ℤ) - dueDate i j ≤ bound i

open Classical in
/-- `1|outtree(l); pᵢ = 1|L_max` as a decision problem over bitstrings. -/
noncomputable def outTreeTimeLagLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OutTreeTimeLagLatenessInstance) x with
  | some i => decide (WellFormed i ∧ OutTreeTimeLagLatenessFeasible i)
  | none => false

/-- **`1|outtree(l); pᵢ = 1|L_max` is NP-complete.** Source: Brucker and Knust (1999);
Brucker and Knust, *Complexity results for scheduling problems*. -/
public theorem_wanted outTreeTimeLagLateness_npComplete :
    outTreeTimeLagLatenessDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L outTreeTimeLagLatenessDec

end MetaMathlibExt.Complexity.NPComplete.OutTreeTimeLagLateness
