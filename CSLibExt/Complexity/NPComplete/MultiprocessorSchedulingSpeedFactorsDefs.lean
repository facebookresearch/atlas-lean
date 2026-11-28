/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS;
M. R. Garey and D. S. Johnson, ""Strong" NP-completeness results: motivation, examples, and
implications", Journal of the ACM 25 (1978), 499-508, doi:10.1145/322077.322090
(MULTIPROCESSOR SCHEDULING is NP-complete in the strong sense);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS8] MULTIPROCESSOR SCHEDULING.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiprocessorSchedulingDefs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors

open MetaMathlibExt.Complexity.NPComplete.MultiprocessorScheduling
  (MultiprocessorSchedulingInstance Task taskLength)

/-- An instance: the task lengths `l(t)` (task `t` is the `t`-th entry), the speed factors (the
`i`-th entry `(a, b)` is `s(i) = a / b`; `m` is their number), and the bound `K`. -/
abbrev MultiprocessorSchedulingSpeedFactorsInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The underlying `MultiprocessorScheduling` instance: the task lengths, `m` and `K`. -/
def toMultiprocessorScheduling (i : MultiprocessorSchedulingSpeedFactorsInstance) :
    MultiprocessorSchedulingInstance :=
  (i.1, i.2.1.length, i.2.2)

/-- The speed factor `s(p)` of processor `p`. -/
def speed (i : MultiprocessorSchedulingSpeedFactorsInstance) (p : Fin i.2.1.length) : ℚ :=
  ((i.2.1.get p).1 : ℚ) / (i.2.1.get p).2

/-- Well-formedness of an instance: the `MultiprocessorScheduling` conditions (positive lengths,
`m ≥ 1`, `K ≥ 1`); every speed factor `a / b` has `0 < b ≤ a`, so `s(i) ≥ 1`; and the first one
is `1`. -/
def WellFormed (i : MultiprocessorSchedulingSpeedFactorsInstance) : Prop :=
  MultiprocessorScheduling.WellFormed (toMultiprocessorScheduling i) ∧
    (∀ s ∈ i.2.1, 0 < s.2 ∧ s.2 ≤ s.1) ∧ ∀ s ∈ i.2.1.head?, s.1 = s.2

/-- Some assignment `f` of tasks to processors has finish time at most `K`: for every processor
`p`, the total length of the tasks assigned to `p`, divided by `s(p)`, is at most `K`. -/
def MultiprocessorSchedulingSpeedFactorsFeasible
    (i : MultiprocessorSchedulingSpeedFactorsInstance) : Prop :=
  ∃ f : Task (toMultiprocessorScheduling i) → Fin i.2.1.length, ∀ p,
    (∑ t ∈ Finset.univ.filter (fun t => f t = p),
        (taskLength (toMultiprocessorScheduling i) t : ℚ)) / speed i p ≤ i.2.2

open Classical in
/-- MULTIPROCESSOR SCHEDULING WITH SPEED FACTORS as a decision problem over bitstrings. -/
noncomputable def multiprocessorSchedulingSpeedFactorsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiprocessorSchedulingSpeedFactorsInstance) x with
  | some i => decide (WellFormed i ∧ MultiprocessorSchedulingSpeedFactorsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultiprocessorSchedulingSpeedFactors
