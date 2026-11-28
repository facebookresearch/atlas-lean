/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IN-TREE TIME LAGS WITH RELEASE DATES (1|intree(l); pᵢ = 1; rᵢ|C_max): definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Single machine problems with
non-negative time-lags", which lists `1|intree(l); pᵢ = 1; rᵢ|C_max` as strongly NP-hard with
the attribution to Brucker and Knust (1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InTreeTimeLagReleaseMakespan

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: the release dates `r₀, …, rₙ₋₁`, the pairs `(i, j)` with `i → j`, the time
lag `l` and the bound `K`. -/
abbrev InTreeTimeLagReleaseMakespanInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` release dates. -/
abbrev Job (i : InTreeTimeLagReleaseMakespanInstance) : Type := Fin i.1.length

/-- The release date `rⱼ` of job `j`. -/
def releaseDate (i : InTreeTimeLagReleaseMakespanInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- The precedence relation: `j → j'` when the pair `(j, j')` is listed. -/
def Prec (i : InTreeTimeLagReleaseMakespanInstance) (j j' : Job i) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2.1

/-- `j` is an immediate predecessor of `j'` (and `j'` an immediate successor of `j`):
`j → j'`, and no job `c` has `j → c → j'`. -/
def ImmediatePredecessor (i : InTreeTimeLagReleaseMakespanInstance) (j j' : Job i) : Prop :=
  Prec i j j' ∧ ∀ c, ¬ (Prec i j c ∧ Prec i c j')

/-- Well-formedness of an instance: every listed pair names two jobs, the listed pairs form a
strict partial order, and the order is an in-tree (every job has at most one immediate
successor). -/
def WellFormed (i : InTreeTimeLagReleaseMakespanInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Job i) (Prec i) ∧
    ∀ j a b, ImmediatePredecessor i j a → ImmediatePredecessor i j b → a = b

/-- Some one-processor schedule `σ` of the unit-time jobs (start times `σ j`, completion
times `σ j + 1`) respects the release dates, satisfies every time lag (`j → j'` implies
`σ j + 1 + l ≤ σ j'`) and has makespan at most `K`. -/
def InTreeTimeLagReleaseMakespanFeasible (i : InTreeTimeLagReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ j, releaseDate i j ≤ σ j) ∧
    (∀ j j', Prec i j j' → σ j + 1 + i.2.2.1 ≤ σ j') ∧ ∀ j, σ j + 1 ≤ i.2.2.2

open Classical in
/-- `1|intree(l); pᵢ = 1; rᵢ|C_max` as a decision problem over bitstrings. -/
noncomputable def inTreeTimeLagReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InTreeTimeLagReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ InTreeTimeLagReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InTreeTimeLagReleaseMakespan
