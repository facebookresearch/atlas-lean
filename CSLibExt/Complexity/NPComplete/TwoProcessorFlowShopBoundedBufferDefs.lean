/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS17] TWO-PROCESSOR
FLOW-SHOP WITH BOUNDED BUFFER (with the definitions of [SS1], [SS14] and [SS15]);
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited
temporary storage", Journal of the ACM 27 (1980), 533-549,
doi:10.1145/322203.322213.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer

/-- An instance: the jobs as pairs `(l(t₁[j]), l(t₂[j]))` of task lengths, the overall
deadline `D`, and the buffer bound `B`. -/
abbrev TwoProcessorFlowShopBoundedBufferInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: `D ∈ ℤ⁺`. -/
def WellFormed (i : TwoProcessorFlowShopBoundedBufferInstance) : Prop :=
  0 < i.2.1

/-- `σ₁` and `σ₂` form a two-processor flow-shop schedule meeting the deadline [SS15]: each
`σᵢ` is a one-processor schedule [SS1] (one-to-one, and `σᵢ j > σᵢ k` implies
`σᵢ j ≥ σᵢ k + l(tᵢ[k])`), the two tasks of each job occupy disjoint intervals, every task
finishes by `D`, and each job starts on processor 2 no earlier than it finishes on
processor 1. -/
def IsFlowShopSchedule (i : TwoProcessorFlowShopBoundedBufferInstance)
    (σ₁ σ₂ : Fin i.1.length → ℕ) : Prop :=
  Function.Injective σ₁ ∧ Function.Injective σ₂ ∧
    (∀ j k, σ₁ k < σ₁ j → σ₁ k + (i.1.get k).1 ≤ σ₁ j) ∧
    (∀ j k, σ₂ k < σ₂ j → σ₂ k + (i.1.get k).2 ≤ σ₂ j) ∧
    (∀ j, Disjoint (Set.Ico (σ₁ j) (σ₁ j + (i.1.get j).1))
      (Set.Ico (σ₂ j) (σ₂ j + (i.1.get j).2))) ∧
    (∀ j, σ₁ j + (i.1.get j).1 ≤ i.2.1 ∧ σ₂ j + (i.1.get j).2 ≤ i.2.1) ∧
    ∀ j, σ₁ j + (i.1.get j).1 ≤ σ₂ j

/-- There is a two-processor flow-shop schedule meeting the deadline such that at every time
`u` at most `B` jobs have finished on processor 1 but not yet started on processor 2. -/
def TwoProcessorFlowShopBoundedBufferFeasible
    (i : TwoProcessorFlowShopBoundedBufferInstance) : Prop :=
  ∃ σ₁ σ₂ : Fin i.1.length → ℕ, IsFlowShopSchedule i σ₁ σ₂ ∧
    ∀ u : ℕ, (Finset.univ.filter fun j => σ₁ j + (i.1.get j).1 ≤ u ∧ u < σ₂ j).card ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER as a decision problem over bitstrings. -/
noncomputable def twoProcessorFlowShopBoundedBufferDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFlowShopBoundedBufferInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorFlowShopBoundedBufferFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer
