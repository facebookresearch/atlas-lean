/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# F2|p_ij=1;t_j|Σw_jC_j (two-machine unit-time flow shop with transportation delays, total weighted
completion time): definitions

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8; recorded in P. Brucker and
S. Knust, "Complexity results for scheduling problems", table "Flow-shop problems with
transportation delays" (minimal NP-hard `F2|p_ij=1;t_i|Σw_iC_i`, Brucker et al. 2004).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopDelaysWeighted

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

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopDelaysWeighted
