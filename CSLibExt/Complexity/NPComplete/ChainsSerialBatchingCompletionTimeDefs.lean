/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIAL BATCHING WITH CHAINS TO MINIMIZE TOTAL COMPLETION TIME: definitions

Source:
S. Albers and P. Brucker, "The complexity of one-machine batching problems", Discrete Applied
Mathematics 47 (1993), 87-107, doi:10.1016/0166-218X(93)90085-3 (`1|chains; s-batch|∑ Cᵢ`);
P. Brucker, *Scheduling Algorithms*, 5th edition, Springer (2007), Sections 2.7 and 8.1 (the
single machine s-batching model) and Table 8.2 (NP-hard serial batching problems), which lists
`1|chains; s-batch|∑ Cᵢ` as NP-hard with the attribution to Albers and Brucker.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTime

/-- An instance: the processing times `p₀, …, pₙ₋₁`, the pairs `(i, j)` with `i → j`, the
set-up time `s` and the bound `K`. -/
abbrev ChainsSerialBatchingCompletionTimeInstance := List ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The jobs of the instance, `Fin n` for `n` processing times. -/
abbrev Job (i : ChainsSerialBatchingCompletionTimeInstance) : Type := Fin i.1.length

/-- The processing time `pⱼ` of job `j`. -/
def processingTime (i : ChainsSerialBatchingCompletionTimeInstance) (j : Job i) : ℕ :=
  i.1.get j

/-- The precedence relation: `j → j'` when the pair `(j, j')` is listed. -/
def Prec (i : ChainsSerialBatchingCompletionTimeInstance) (j j' : Job i) : Prop :=
  ((j : ℕ), (j' : ℕ)) ∈ i.2.1

/-- `j` is an immediate predecessor of `j'` (and `j'` an immediate successor of `j`):
`j → j'`, and no job `c` has `j → c → j'`. -/
def ImmediatePredecessor (i : ChainsSerialBatchingCompletionTimeInstance) (j j' : Job i) :
    Prop :=
  Prec i j j' ∧ ∀ c, ¬ (Prec i j c ∧ Prec i c j')

/-- The completion time of job `j` when job `j'` is put in batch `β j'`: one set-up for each
nonempty batch with index at most `β j`, plus the processing times of all jobs in those
batches. -/
def completionTime (i : ChainsSerialBatchingCompletionTimeInstance) (β : Job i → ℕ)
    (j : Job i) : ℕ :=
  i.2.2.1 * ((Finset.univ.image β).filter fun b => b ≤ β j).card +
    ∑ j' ∈ Finset.univ.filter (fun j' => β j' ≤ β j), processingTime i j'

/-- Well-formedness of an instance: every listed pair names two jobs, the listed pairs form a
strict partial order, and the order consists of chains (every job has at most one immediate
predecessor and at most one immediate successor). -/
def WellFormed (i : ChainsSerialBatchingCompletionTimeInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧
    IsStrictOrder (Job i) (Prec i) ∧
    (∀ j a b, ImmediatePredecessor i a j → ImmediatePredecessor i b j → a = b) ∧
    ∀ j a b, ImmediatePredecessor i j a → ImmediatePredecessor i j b → a = b

/-- Some batching compatible with the precedence constraints (`j → j'` implies that `j'` is
not in an earlier batch than `j`) has total completion time at most `K`. -/
def ChainsSerialBatchingCompletionTimeFeasible
    (i : ChainsSerialBatchingCompletionTimeInstance) : Prop :=
  ∃ β : Job i → ℕ, (∀ j j', Prec i j j' → β j ≤ β j') ∧
    ∑ j, completionTime i β j ≤ i.2.2.2

open Classical in
/-- SERIAL BATCHING WITH CHAINS TO MINIMIZE TOTAL COMPLETION TIME as a decision problem over
bitstrings. -/
noncomputable def chainsSerialBatchingCompletionTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainsSerialBatchingCompletionTimeInstance) x with
  | some i => decide (WellFormed i ∧ ChainsSerialBatchingCompletionTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainsSerialBatchingCompletionTime
