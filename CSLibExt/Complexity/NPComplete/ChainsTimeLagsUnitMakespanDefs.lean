/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE MAKESPAN with chains, time lags and unit processing times: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsTimeLagsUnitMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the processing times `p₀, …, pₙ₋₁` (one per job), the list of triples
`(i, j, lᵢⱼ)` of time-lagged pairs, and the bound `K`. -/
abbrev ChainsTimeLagsUnitMakespanInstance := List ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed processing times. -/
abbrev Job (i : ChainsTimeLagsUnitMakespanInstance) : Type := Fin i.1.length

/-- The processing time `pⱼ` of job `j`. -/
def processingTime (i : ChainsTimeLagsUnitMakespanInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- The pair relation: some triple `(j, k, l)` is listed. -/
def Arc (i : ChainsTimeLagsUnitMakespanInstance) (j k : Job i) : Prop :=
  ∃ l, ((j : ℕ), (k : ℕ), l) ∈ i.2.1

/-- Well-formedness of an instance: every processing time is `1`, every listed pair joins two
jobs, no job is the first job of two listed pairs, no job is the second job of two listed pairs,
and the pairs have no cycle. -/
def WellFormed (i : ChainsTimeLagsUnitMakespanInstance) : Prop :=
  (∀ p ∈ i.1, p = 1) ∧ (∀ a ∈ i.2.1, a.1 < i.1.length ∧ a.2.1 < i.1.length) ∧
    (i.2.1.map Prod.fst).Nodup ∧ (i.2.1.map fun a => a.2.1).Nodup ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some one-processor schedule `σ` satisfies every time lag, `σ(j) + pⱼ + l ≤ σ(k)` for each
listed triple `(j, k, l)`, and has makespan `max (σ(j) + pⱼ)` at most `K`. -/
def ChainsTimeLagsUnitMakespanFeasible (i : ChainsTimeLagsUnitMakespanInstance) : Prop :=
  ∃ σ : Job i → ℕ, IsOneProcessorSchedule (processingTime i) σ ∧
    (∀ j k : Job i, ∀ l, ((j : ℕ), (k : ℕ), l) ∈ i.2.1 → σ j + processingTime i j + l ≤ σ k) ∧
    ∀ j, σ j + processingTime i j ≤ i.2.2

open Classical in
/-- SINGLE-MACHINE MAKESPAN with chains, time lags and unit processing times as a decision
problem over bitstrings. -/
noncomputable def chainsTimeLagsUnitMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsTimeLagsUnitMakespanInstance) x with
  | some i => decide (WellFormed i ∧ ChainsTimeLagsUnitMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsTimeLagsUnitMakespan
