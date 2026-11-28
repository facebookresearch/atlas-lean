/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR UNIT-TIME FLOW-SHOP TOTAL TARDINESS WITH CHAINS: definitions

Source:
P. Brucker and S. Knust, "Complexity results for single-machine problems with positive
finish-start time-lags", Computing 63 (1999), 299-316, doi:10.1007/s006070050036
(`F2|pᵢⱼ = 1, chains|∑ Tⱼ` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems without preemption" (`F2|pᵢⱼ = 1; chains|∑ Tᵢ`, minimal NP-hard,
credited to Brucker and Knust 1999).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardiness

/-- An instance: the due dates, job `j` having the `j`-th listed due date `dⱼ`, the arcs
`(j, k)` of the chains (`j` the immediate predecessor of `k`), and the bound `K`. -/
abbrev TwoProcessorUnitFlowShopChainsTardinessInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed due dates. -/
abbrev Job (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Type := Fin i.1.length

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : TwoProcessorUnitFlowShopChainsTardinessInstance) (j : Job i) : ℕ := i.1.get j

/-- The arc relation of the chains: `j` is the immediate predecessor of `k` when the pair
`(j, k)` is listed. -/
def Arc (i : TwoProcessorUnitFlowShopChainsTardinessInstance) (j k : Job i) : Prop :=
  ((j : ℕ), (k : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: every arc names two jobs, no two distinct arcs share their
tail (at most one immediate successor) or their head (at most one immediate predecessor), and
the arcs have no cycle. -/
def WellFormed (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1.length ∧ a.2 < i.1.length) ∧
    (∀ a ∈ i.2.1, ∀ b ∈ i.2.1, a.1 = b.1 → a = b) ∧
    (∀ a ∈ i.2.1, ∀ b ∈ i.2.1, a.2 = b.2 → a = b) ∧
    ∀ j, ¬ Relation.TransGen (Arc i) j j

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂` for unit operations,
runs one operation at a time on each machine, starts each job on `M₂` only after it is
completed on `M₁`, starts job `k` on `M₁` only after its immediate predecessor `j` is completed
on `M₂`, and has total tardiness `∑ⱼ (s₂ j + 1 - dⱼ)` (truncated subtraction) at most `K`. -/
def TwoProcessorUnitFlowShopChainsTardinessFeasible
    (i : TwoProcessorUnitFlowShopChainsTardinessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + 1 ≤ s₁ k ∨ s₁ k + 1 ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + 1 ≤ s₂ k ∨ s₂ k + 1 ≤ s₂ j) ∧
    (∀ j, s₁ j + 1 ≤ s₂ j) ∧
    (∀ j k, Arc i j k → s₂ j + 1 ≤ s₁ k) ∧
    ∑ j, (s₂ j + 1 - dueDate i j) ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR UNIT-TIME FLOW-SHOP TOTAL TARDINESS WITH CHAINS as a decision problem over
bitstrings. -/
noncomputable def twoProcessorUnitFlowShopChainsTardinessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitFlowShopChainsTardinessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitFlowShopChainsTardinessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitFlowShopChainsTardiness
