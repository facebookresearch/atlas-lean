/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR TASKS WITH RELEASE DATES `P2|r_i;size_i|Cmax`: definitions

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (only the abstract was
available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|r_i;size_i|C_max` (minimal NP-hard in the
strong sense, citing Lee and Cai 1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDates

/-- An instance: the tasks `(p_i, size_i, r_i)` (processing time, size, release date), one per
entry, and the bound `K`. -/
abbrev TwoProcessorTaskSizeReleaseDatesInstance := List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness: every task has size `1` or `2`. -/
def WellFormed (i : TwoProcessorTaskSizeReleaseDatesInstance) : Prop :=
  ∀ t ∈ i.1, 1 ≤ t.2.1 ∧ t.2.1 ≤ 2

/-- There are start times `s` such that every task starts no earlier than its release date and
completes by `K`, and at every time `t` the tasks running at `t` (`s j ≤ t < s j + p_j`) have
total size at most `2`. -/
def TwoProcessorTaskSizeReleaseDatesFeasible (i : TwoProcessorTaskSizeReleaseDatesInstance) :
    Prop :=
  ∃ s : Fin i.1.length → ℕ, (∀ j, (i.1.get j).2.2 ≤ s j ∧ s j + (i.1.get j).1 ≤ i.2) ∧
    ∀ t : ℕ, ∑ j ∈ Finset.univ.filter (fun j => s j ≤ t ∧ t < s j + (i.1.get j).1),
      (i.1.get j).2.1 ≤ 2

open Classical in
/-- `P2|r_i;size_i|Cmax` as a decision problem over bitstrings. -/
noncomputable def twoProcessorTaskSizeReleaseDatesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTaskSizeReleaseDatesInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTaskSizeReleaseDatesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeReleaseDates
