/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE FLOW SHOP WITH TWO DELAY VALUES is NP-complete

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Theorem 1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Flow-shop problems with transportation delays" (records the problem
`F2|tⱼ ∈ {T₁, T₂}|Cmax` as minimal NP-hard, citing Yu (1996)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValues

/-!
# TWO-MACHINE FLOW SHOP WITH TWO DELAY VALUES is NP-complete

INSTANCE: two machines `M₁`, `M₂`, each available at time zero and processing at most one job
at a time; `n` jobs, job `j` with processing time `p₁ⱼ ∈ ℤ₀⁺` on `M₁` and `p₂ⱼ ∈ ℤ₀⁺` on `M₂`
and a delay `lⱼ`, the minimum amount of time between the completion of job `j` on `M₁` and its
start on `M₂`, where every delay equals one of two given values `T₁, T₂ ∈ ℤ₀⁺`; and a bound
`K ∈ ℤ₀⁺`. QUESTION: is there a feasible schedule whose makespan (the completion time of the
last job on `M₂`) is at most `K`?

This is the decision version of `F2|lⱼ ∈ {T₁, T₂}|Cmax` (in the Brucker-Knust tables
`F2|tⱼ ∈ {T₁, T₂}|Cmax`, delays as transportation times). Delays occupy no machine, and any
number of jobs may be between the machines at once. Schedules need not process the jobs in the
same order on both machines. Yu proves the problem strongly NP-hard already when
`p₁ⱼ = p₂ⱼ` for every job and the delays take the two values `l` and `0`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-MACHINE FLOW SHOP WITH TWO DELAY VALUES is NP-complete.** Source: Yu (1996),
Chapter 2, Theorem 1; Brucker and Knust (classification tables). -/
public theorem_wanted twoMachineFlowShopTwoDelayValues_npComplete :
    twoMachineFlowShopTwoDelayValuesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineFlowShopTwoDelayValuesDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValues
