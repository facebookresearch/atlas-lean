/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-MACHINE OPEN SHOP WITH TWO DELAY VALUES is NP-complete

Source:
W. Yu, *The two-machine flow shop problem with delays and the one-machine total tardiness
problem*, PhD thesis, Technische Universiteit Eindhoven (1996), Chapter 2, Section 2.5,
Theorem 4 (pp. 13-16);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück
(online tables), class "Open-shop problems with transportation delays" (records the problem
`O2|tᵢ ∈ {T₁, T₂}|Cmax` as minimal NP-hard in the strong sense, citing Yu (1996)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TwoMachineFlowShopTwoDelayValuesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopTwoDelayValues

open TwoMachineFlowShopTwoDelayValues (TwoMachineFlowShopTwoDelayValuesInstance WellFormed)

/-!
# TWO-MACHINE OPEN SHOP WITH TWO DELAY VALUES is NP-complete

INSTANCE: two machines `M₁`, `M₂` in an open shop, each processing at most one operation at a
time; `n` jobs, job `j` consisting of an operation of processing time `p₁ⱼ ∈ ℤ₀⁺` on `M₁` and an
operation of processing time `p₂ⱼ ∈ ℤ₀⁺` on `M₂`, which may be processed in either order, and a
delay `lⱼ`: between the completion of the operation of job `j` processed first and the start of
its operation processed second, at least `lⱼ` time units must elapse; every delay equals one of
two given values `T₁, T₂ ∈ ℤ₀⁺`; and a bound `K ∈ ℤ₀⁺`. QUESTION: is there a feasible schedule
whose makespan (the largest completion time of an operation) is at most `K`?

This is the decision version of `O2|tᵢ ∈ {T₁, T₂}|Cmax` in the Brucker-Knust tables, where the
delay is the transportation time of job `i` between the two machines, the same in both
directions. Delays occupy no machine, and any number of jobs may be between the machines at
once. Yu proves the problem strongly NP-hard already when `p₁ⱼ = p₂ⱼ` for every job.

The instance (the two delay values `T₁`, `T₂`, the jobs `(p₁ⱼ, p₂ⱼ, lⱼ)` listed one per entry,
and `K`) and the well-formedness condition (every delay is `T₁` or `T₂`) are those of the
two-machine flow shop with two delay values (`TwoMachineFlowShopTwoDelayValuesWanted`). Only the
schedule differs: in the open shop each job chooses which of its operations comes first.

Start times are natural numbers: once the order of the operations on each machine and of the two
operations of each job is fixed, every constraint is a difference constraint with integer
constants, and such a system has an integer solution whenever it has a real one. Numbers use the
binary encoding. Membership in NP is the certificate argument: the `2n` start times of a
schedule, each at most `K`, are checked in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **TWO-MACHINE OPEN SHOP WITH TWO DELAY VALUES is NP-complete.** Source: Yu (1996),
Chapter 2, Theorem 4; Brucker and Knust (classification tables). -/
public theorem_wanted twoMachineOpenShopTwoDelayValues_npComplete :
    twoMachineOpenShopTwoDelayValuesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoMachineOpenShopTwoDelayValuesDec

end MetaMathlibExt.Complexity.NPComplete.TwoMachineOpenShopTwoDelayValues
