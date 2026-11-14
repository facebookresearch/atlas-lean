/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS17] TWO-PROCESSOR
FLOW-SHOP WITH BOUNDED BUFFER (with the definitions of [SS1], [SS14] and [SS15]);
C. H. Papadimitriou and P. C. Kanellakis, "Flowshop scheduling with limited
temporary storage", Journal of the ACM 27 (1980), 533-549,
doi:10.1145/322203.322213.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer

/-!
# TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete

INSTANCE: a set `J` of jobs, each job `j ∈ J` consisting of two tasks `t₁[j]` and `t₂[j]`
(with `tᵢ[j]` to be executed by processor `i`), a length `l(t) ∈ ℤ₀⁺` for each such task `t`,
an overall deadline `D ∈ ℤ⁺`, and a "buffer bound" `B ∈ ℤ₀⁺` (this is FLOW-SHOP SCHEDULING
with `m = 2`, plus `B`).
QUESTION: is there a flow-shop schedule for `J` that meets the overall deadline and such that,
for all `u ≥ 0`, the number of jobs `j ∈ J` for which both `σ₁(j) + l(t₁[j]) ≤ u` and
`σ₂(j) > u` does not exceed `B`?

Following Garey and Johnson, a flow-shop schedule [SS15] meeting the deadline is an open-shop
schedule [SS14] meeting the deadline, i.e. one-processor schedules `σ₁, σ₂ : J → ℤ₀⁺` (each
one-to-one, with `σᵢ(j) > σᵢ(k)` implying `σᵢ(j) ≥ σᵢ(k) + l(tᵢ[k])` [SS1]) such that for
each `j ∈ J` the intervals `[σ₁(j), σ₁(j) + l(t₁[j]))` and `[σ₂(j), σ₂(j) + l(t₂[j]))` are
disjoint and `σᵢ(j) + l(tᵢ[j]) ≤ D`, with the additional constraint
`σ₂(j) ≥ σ₁(j) + l(t₁[j])` for each `j ∈ J`. A job counted at time `u` has finished on
processor 1 but not yet started on processor 2, so it occupies the buffer.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-PROCESSOR FLOW-SHOP WITH BOUNDED BUFFER is NP-complete.** Source: Garey and
Johnson (1979), [SS17]; Papadimitriou and Kanellakis (1980). -/
public theorem_wanted twoProcessorFlowShopBoundedBuffer_npComplete :
    twoProcessorFlowShopBoundedBufferDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorFlowShopBoundedBufferDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorFlowShopBoundedBuffer
