/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO DEDICATED PROCESSORS WITH RELEASE DATES `P2|r_i;fix_i|Cmax`: definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994), 259-272,
doi:10.1016/0166-218X(94)90012-4, Theorem 2.8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `mpt` (multiprocessor tasks), entry
`P2|r_i;fix_i|C_max` (minimal NP-hard in the strong sense, citing Hoogeveen et al. 1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorReleaseDates

/-- An instance: the tasks `(p_i, fix_i, r_i)` (processing time, processors used, release date),
one per entry, and the bound `K`. -/
abbrev TwoDedicatedProcessorReleaseDatesInstance := List (ℕ × List ℕ × ℕ) × ℕ

/-- Well-formedness: every task has a positive processing time and uses a nonempty set of
processors, listed without repetitions, all among the two processors `0, 1`. -/
def WellFormed (i : TwoDedicatedProcessorReleaseDatesInstance) : Prop :=
  ∀ t ∈ i.1, 0 < t.1 ∧ t.2.1 ≠ [] ∧ t.2.1.Nodup ∧ ∀ k ∈ t.2.1, k < 2

/-- There are start times `s` such that every task starts no earlier than its release date and
completes by `K`, and any two different tasks with a common processor are processed in disjoint
time intervals. -/
def TwoDedicatedProcessorReleaseDatesFeasible (i : TwoDedicatedProcessorReleaseDatesInstance) :
    Prop :=
  ∃ s : Fin i.1.length → ℕ, (∀ j, (i.1.get j).2.2 ≤ s j ∧ s j + (i.1.get j).1 ≤ i.2) ∧
    ∀ j j', j ≠ j' → (∃ k ∈ (i.1.get j).2.1, k ∈ (i.1.get j').2.1) →
      s j + (i.1.get j).1 ≤ s j' ∨ s j' + (i.1.get j').1 ≤ s j

open Classical in
/-- `P2|r_i;fix_i|Cmax` as a decision problem over bitstrings. -/
noncomputable def twoDedicatedProcessorReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoDedicatedProcessorReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoDedicatedProcessorReleaseDatesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDedicatedProcessorReleaseDates
