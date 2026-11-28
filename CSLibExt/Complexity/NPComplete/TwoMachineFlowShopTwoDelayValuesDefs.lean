/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE FLOW SHOP WITH TWO DELAY VALUES: definitions

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Theorem 1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Flow-shop problems with transportation delays" (records the problem
`F2|tⱼ ∈ {T₁, T₂}|Cmax` as minimal NP-hard, citing Yu (1996)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValues

/-- An instance: the two delay values `T₁`, `T₂`, the jobs `(p₁ⱼ, p₂ⱼ, lⱼ)`, and the bound `K`. -/
abbrev TwoMachineFlowShopTwoDelayValuesInstance := ℕ × ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every job's delay is `T₁` or `T₂`. -/
def WellFormed (i : TwoMachineFlowShopTwoDelayValuesInstance) : Prop :=
  ∀ job ∈ i.2.2.1, job.2.2 = i.1 ∨ job.2.2 = i.2.1

/-- A schedule with makespan at most `K`: start times `σ₁ j` on `M₁` and `σ₂ j` on `M₂` such
that every job completes on `M₂` by `K`, each machine processes one job at a time, and job `j`
starts on `M₂` no earlier than `lⱼ` after its completion on `M₁`. -/
def TwoMachineFlowShopTwoDelayValuesFeasible
    (i : TwoMachineFlowShopTwoDelayValuesInstance) : Prop :=
  ∃ σ₁ σ₂ : ℕ → ℕ,
    (∀ j < i.2.2.1.length, σ₂ j + (i.2.2.1.getD j (0, 0, 0)).2.1 ≤ i.2.2.2) ∧
    (∀ j < i.2.2.1.length, ∀ k < i.2.2.1.length, j ≠ k →
      σ₁ j + (i.2.2.1.getD j (0, 0, 0)).1 ≤ σ₁ k ∨
        σ₁ k + (i.2.2.1.getD k (0, 0, 0)).1 ≤ σ₁ j) ∧
    (∀ j < i.2.2.1.length, ∀ k < i.2.2.1.length, j ≠ k →
      σ₂ j + (i.2.2.1.getD j (0, 0, 0)).2.1 ≤ σ₂ k ∨
        σ₂ k + (i.2.2.1.getD k (0, 0, 0)).2.1 ≤ σ₂ j) ∧
    ∀ j < i.2.2.1.length,
      σ₁ j + (i.2.2.1.getD j (0, 0, 0)).1 + (i.2.2.1.getD j (0, 0, 0)).2.2 ≤ σ₂ j

open Classical in
/-- TWO-MACHINE FLOW SHOP WITH TWO DELAY VALUES as a decision problem over bitstrings. -/
noncomputable def twoMachineFlowShopTwoDelayValuesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoMachineFlowShopTwoDelayValuesInstance) x with
  | some i => decide (WellFormed i ∧ TwoMachineFlowShopTwoDelayValuesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValues
