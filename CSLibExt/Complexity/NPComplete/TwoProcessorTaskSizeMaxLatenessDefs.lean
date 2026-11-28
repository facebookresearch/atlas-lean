/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ONE- AND TWO-PROCESSOR TASKS ON TWO PROCESSORS, maximum lateness (`P2|size_i|Lmax`): definitions

Source:
C.-Y. Lee and X. Cai, "Scheduling one and two-processor tasks on two parallel processors",
IIE Transactions 31 (1999), 445-455, doi:10.1080/07408179908969847 (Appendix);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor tasks on parallel processors" (`P2|size_i|L_max`, minimal NP-hard in the
strong sense, citing Lee and Cai 1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeMaxLateness

/-- An instance: the tasks, task `j` being the `j`-th triple `(p_j, size_j, d_j)` of its
processing time, its size and its due date, and the bound `K` as a pair `(K⁺, K⁻)` with
`K = K⁺ - K⁻`. -/
abbrev TwoProcessorTaskSizeMaxLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: there is at least one task, and every task has size `1` or
`2`. -/
def WellFormed (i : TwoProcessorTaskSizeMaxLatenessInstance) : Prop :=
  i.1 ≠ [] ∧ ∀ x ∈ i.1, x.2.1 = 1 ∨ x.2.1 = 2

/-- Some schedule, with start times `S j` and processor sets `π j ⊆ {0, 1}` of `size_j`
processors, runs two different tasks that share a processor during disjoint intervals
`[S j, S j + p_j)`, and completes every task `j` with lateness `C_j - d_j ≤ K⁺ - K⁻`, that is
`S j + p_j + K⁻ ≤ d_j + K⁺`. -/
def TwoProcessorTaskSizeMaxLatenessFeasible (i : TwoProcessorTaskSizeMaxLatenessInstance) :
    Prop :=
  ∃ S : Fin i.1.length → ℕ, ∃ π : Fin i.1.length → Finset (Fin 2),
    (∀ j, (π j).card = (i.1.get j).2.1) ∧
    (∀ j k, j ≠ k → ¬ Disjoint (π j) (π k) →
      Disjoint (Finset.Ico (S j) (S j + (i.1.get j).1))
        (Finset.Ico (S k) (S k + (i.1.get k).1))) ∧
    ∀ j, S j + (i.1.get j).1 + i.2.2 ≤ (i.1.get j).2.2 + i.2.1

open Classical in
/-- `P2|size_i|Lmax` as a decision problem over bitstrings. -/
noncomputable def twoProcessorTaskSizeMaxLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorTaskSizeMaxLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorTaskSizeMaxLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorTaskSizeMaxLateness
