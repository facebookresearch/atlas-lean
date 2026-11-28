/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2||Lmax: definitions

Source:
E. L. Lawler, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Minimizing maximum lateness in a
two-machine open shop", Mathematics of Operations Research 6 (1981), 153-158,
doi:10.1287/moor.6.1.153; Erratum, Mathematics of Operations Research 7 (1982), 635,
doi:10.1287/moor.7.4.635 (the nonpreemptive problem is NP-hard);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Open-shop problems without preemption" (`O2||L_max`, minimal NP-hard in the strong sense,
credited to Lawler, Lenstra, and Rinnooy Kan 1981, 1982).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TwoProcessorFlowShopMaximumLatenessDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMaximumLateness

open TwoProcessorFlowShopMaximumLateness
  (TwoProcessorFlowShopMaximumLatenessInstance Job time₁ time₂ dueDate WellFormed)

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂`, runs one operation at
a time on each machine, never runs the two operations of a job at the same time, and completes
both operations of every job `j` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def TwoProcessorOpenShopMaximumLatenessFeasible
    (i : TwoProcessorFlowShopMaximumLatenessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + time₁ i j ≤ s₁ k ∨ s₁ k + time₁ i k ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + time₂ i j ≤ s₂ k ∨ s₂ k + time₂ i k ≤ s₂ j) ∧
    (∀ j, s₁ j + time₁ i j ≤ s₂ j ∨ s₂ j + time₂ i j ≤ s₁ j) ∧
    ∀ j, s₁ j + time₁ i j + i.2.2 ≤ dueDate i j + i.2.1 ∧
      s₂ j + time₂ i j + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- OPEN SHOP O2||Lmax as a decision problem over bitstrings. -/
noncomputable def twoProcessorOpenShopMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorFlowShopMaximumLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopMaximumLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMaximumLateness
