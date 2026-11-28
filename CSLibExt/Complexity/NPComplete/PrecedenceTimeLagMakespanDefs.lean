/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE SCHEDULING WITH PRECEDENCE TIME LAGS (1|prec(l); pᵢ = 1|C_max): definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PrecedenceTimeLagMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

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

end MetaMathlibExt.Complexity.NPComplete.PrecedenceTimeLagMakespan
