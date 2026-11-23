/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2|p_ij=1;t_j|Σw_jC_j (two-machine unit-time flow shop with transportation delays, total weighted
completion time) is NP-complete

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8; recorded in P. Brucker and
S. Knust, "Complexity results for scheduling problems", table "Flow-shop problems with
transportation delays" (minimal NP-hard `F2|p_ij=1;t_i|Σw_iC_i`, Brucker et al. 2004).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopDelaysWeighted

/-!
# F2|p_ij=1;t_j|Σw_jC_j is NP-complete

INSTANCE: two machines `M₁, M₂` in a flow shop and jobs `j`, each consisting of an operation on
`M₁` followed by an operation on `M₂`, every operation of unit length (`pᵢⱼ = 1`), each machine
processing at most one operation at a time; a transportation delay `tⱼ ∈ ℤ₀⁺` per job: the
operation on `M₂` cannot start before `tⱼ` time units have elapsed after the operation on `M₁`
is completed (delays use no machine, and any number of jobs may be in transit at once); a weight
`wⱼ ∈ ℤ₀⁺` per job; and a bound `K`.
QUESTION: is there a feasible schedule with total weighted completion time `Σⱼ wⱼ Cⱼ ≤ K`, where
`Cⱼ` is the completion time of job `j` (of its operation on `M₂`)?

A schedule is given by integer start times `s₁ⱼ` on `M₁` and `s₂ⱼ` on `M₂`; unit operations on
one machine do not overlap (`s j + 1 ≤ s k` or `s k + 1 ≤ s j` for distinct jobs `j, k`), the
delay condition is `s₁ⱼ + 1 + tⱼ ≤ s₂ⱼ`, and `Cⱼ = s₂ⱼ + 1`. Every decoded instance is well
formed. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the jobs `(tⱼ, wⱼ)` (transportation delay, weight) and the bound `K`. -/
abbrev UnitFlowShopDelaysWeightedInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness: every instance (all data are non-negative integers). -/
def WellFormed (_ : UnitFlowShopDelaysWeightedInstance) : Prop := True

/-- Some unit-time schedule `s₁, s₂` (start times on `M₁`, `M₂`) without overlaps on either
machine and respecting the transportation delays has `Σⱼ wⱼ (s₂ⱼ + 1) ≤ K`. -/
def UnitFlowShopDelaysWeightedFeasible (i : UnitFlowShopDelaysWeightedInstance) :
    Prop :=
  ∃ s₁ s₂ : Fin i.1.length → ℕ,
    (∀ j k, j ≠ k → s₁ j + 1 ≤ s₁ k ∨ s₁ k + 1 ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + 1 ≤ s₂ k ∨ s₂ k + 1 ≤ s₂ j) ∧
    (∀ j, s₁ j + 1 + (i.1.get j).1 ≤ s₂ j) ∧
    ∑ j, (i.1.get j).2 * (s₂ j + 1) ≤ i.2

open Classical in
/-- F2|p_ij=1;t_j|Σw_jC_j as a decision
problem over bitstrings. -/
noncomputable def unitFlowShopDelaysWeightedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopDelaysWeightedInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopDelaysWeightedFeasible i)
  | none => false

/-- **F2|p_ij=1;t_j|Σw_jC_j is NP-complete.**
Source: Brucker, Cheng, Knust and Shakhlevich (2004). -/
public theorem_wanted unitFlowShopDelaysWeighted_npComplete :
    unitFlowShopDelaysWeightedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitFlowShopDelaysWeightedDec

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopDelaysWeighted
