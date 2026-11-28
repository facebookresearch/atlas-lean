/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SINGLE-MACHINE WEIGHTED COMPLETION TIME with chains, unit processing times and release dates: definitions
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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.SequencingToMinimizeWeightedTardinessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsUnitReleaseWeightedCompletion

open SequencingToMinimizeWeightedTardiness (IsOneProcessorSchedule)

/-- An instance: one pair `(rⱼ, wⱼ)` of release date and weight per job, the list of arcs
`(j, k)` of the precedence digraph, and the bound `K`. -/
abbrev ChainsUnitReleaseWeightedCompletionInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed pairs `(rⱼ, wⱼ)`. -/
abbrev Job (i : ChainsUnitReleaseWeightedCompletionInstance) : Type := Fin i.1.length

/-- The release date `rⱼ` of job `j`. -/
def releaseDate (i : ChainsUnitReleaseWeightedCompletionInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The weight `wⱼ` of job `j`. -/
def weight (i : ChainsUnitReleaseWeightedCompletionInstance) (j : Job i) : ℕ :=
  (i.1.get j).2

/-- The arc relation of the precedence digraph: the pair `(j, k)` is listed. -/
def Arc (i : ChainsUnitReleaseWeightedCompletionInstance) (j k : Job i) : Prop :=
  ((j : ℕ), (k : ℕ)) ∈ i.2.1

/-- The precedence relation `Jⱼ → Jₖ`: there is a directed path from `Jⱼ` to `Jₖ`. -/
def Precedes (i : ChainsUnitReleaseWeightedCompletionInstance) (j k : Job i) : Prop :=
  Relation.TransGen (Arc i) j k

/-- Well-formedness of an instance: every arc joins two jobs, no job is the tail of two listed
arcs (outdegree at most one), no job is the head of two listed arcs (indegree at most one), and
the digraph is acyclic. -/
def WellFormed (i : ChainsUnitReleaseWeightedCompletionInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1.length ∧ a.2 < i.1.length) ∧
    (i.2.1.map Prod.fst).Nodup ∧ (i.2.1.map Prod.snd).Nodup ∧
    ∀ j, ¬ Precedes i j j

/-- Some one-processor schedule `σ` of unit-time jobs starts every job no earlier than its
release date, completes `Jⱼ` before `Jₖ` starts whenever `Jⱼ → Jₖ`, and has total weighted
completion time `∑ⱼ wⱼ (σ(j) + 1)` at most `K`. -/
def ChainsUnitReleaseWeightedCompletionFeasible
    (i : ChainsUnitReleaseWeightedCompletionInstance) : Prop :=
  ∃ σ : Job i → ℕ, IsOneProcessorSchedule (fun _ => 1) σ ∧
    (∀ j, releaseDate i j ≤ σ j) ∧
    (∀ j k, Precedes i j k → σ j + 1 ≤ σ k) ∧
    ∑ j, weight i j * (σ j + 1) ≤ i.2.2

open Classical in
/-- SINGLE-MACHINE WEIGHTED COMPLETION TIME with chains, unit processing times and release dates
as a decision problem over bitstrings. -/
noncomputable def chainsUnitReleaseWeightedCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsUnitReleaseWeightedCompletionInstance) x with
  | some i => decide (WellFormed i ∧ ChainsUnitReleaseWeightedCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsUnitReleaseWeightedCompletion
