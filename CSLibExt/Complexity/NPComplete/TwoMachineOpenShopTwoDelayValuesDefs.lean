/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE OPEN SHOP WITH TWO DELAY VALUES: definitions

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Section 2.5,
Theorem 4 (pp. 13-16);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Open-shop problems with transportation delays" (records the problem
`O2|tᵢ ∈ {T₁, T₂}|Cmax` as minimal NP-hard in the strong sense, citing Yu (1996)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValuesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopTwoDelayValues

open TwoMachineFlowShopTwoDelayValues (TwoMachineFlowShopTwoDelayValuesInstance WellFormed)

/-- A schedule with makespan at most `K`: start times `σ₁ j` on `M₁` and `σ₂ j` on `M₂` such
that every operation completes by `K`, each machine processes one operation at a time, and for
each job `j`, either its operation on `M₂` starts at least `lⱼ` after its operation on `M₁` is
completed, or its operation on `M₁` starts at least `lⱼ` after its operation on `M₂` is
completed. -/
def TwoMachineOpenShopTwoDelayValuesFeasible
    (i : TwoMachineFlowShopTwoDelayValuesInstance) : Prop :=
  ∃ σ₁ σ₂ : ℕ → ℕ,
    (∀ j < i.2.2.1.length,
      σ₁ j + (i.2.2.1.getD j (0, 0, 0)).1 ≤ i.2.2.2 ∧
        σ₂ j + (i.2.2.1.getD j (0, 0, 0)).2.1 ≤ i.2.2.2) ∧
    (∀ j < i.2.2.1.length, ∀ k < i.2.2.1.length, j ≠ k →
      σ₁ j + (i.2.2.1.getD j (0, 0, 0)).1 ≤ σ₁ k ∨
        σ₁ k + (i.2.2.1.getD k (0, 0, 0)).1 ≤ σ₁ j) ∧
    (∀ j < i.2.2.1.length, ∀ k < i.2.2.1.length, j ≠ k →
      σ₂ j + (i.2.2.1.getD j (0, 0, 0)).2.1 ≤ σ₂ k ∨
        σ₂ k + (i.2.2.1.getD k (0, 0, 0)).2.1 ≤ σ₂ j) ∧
    ∀ j < i.2.2.1.length,
      σ₁ j + (i.2.2.1.getD j (0, 0, 0)).1 + (i.2.2.1.getD j (0, 0, 0)).2.2 ≤ σ₂ j ∨
        σ₂ j + (i.2.2.1.getD j (0, 0, 0)).2.1 + (i.2.2.1.getD j (0, 0, 0)).2.2 ≤ σ₁ j

open Classical in
/-- TWO-MACHINE OPEN SHOP WITH TWO DELAY VALUES as a decision problem over bitstrings. -/
noncomputable def twoMachineOpenShopTwoDelayValuesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopTwoDelayValuesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineOpenShopTwoDelayValuesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopTwoDelayValues
