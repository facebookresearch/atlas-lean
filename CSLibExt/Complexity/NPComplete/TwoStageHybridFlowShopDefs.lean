/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-STAGE HYBRID FLOW SHOP: definitions

Source:
J. N. D. Gupta, "Two-stage, hybrid flowshop scheduling problem", Journal of the Operational
Research Society 39 (1988), 359-364, doi:10.1057/jors.1988.63 (the model; NP-completeness of the
two-stage problem with identical parallel machines at each stage);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION (NP-hardness of the restriction
stated here, by the reduction in the module docstring).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoStageHybridFlowShop

/-- An instance: the jobs, job `j` given as `(a_j, b_j)` (stage-1 and stage-2 processing
times), and the bound `K` on the makespan. -/
abbrev TwoStageHybridFlowShopInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: all processing times are positive. -/
def WellFormed (i : TwoStageHybridFlowShopInstance) : Prop :=
  ∀ job ∈ i.1, 0 < job.1 ∧ 0 < job.2

/-- There is a nonpreemptive schedule with makespan at most `K`: a stage-1 machine `μ j` for
every job and start times `s₁ j`, `s₂ j` such that distinct jobs on the same stage-1 machine
and distinct jobs at stage 2 occupy disjoint intervals, each job starts stage 2 after finishing
stage 1, and every job finishes stage 2 by `K`. -/
def TwoStageHybridFlowShopFeasible (i : TwoStageHybridFlowShopInstance) : Prop :=
  ∃ (μ : Fin i.1.length → Fin 2) (s₁ s₂ : Fin i.1.length → ℕ),
    (∀ j k, j ≠ k → μ j = μ k →
      s₁ j + (i.1.get j).1 ≤ s₁ k ∨ s₁ k + (i.1.get k).1 ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + (i.1.get j).2 ≤ s₂ k ∨ s₂ k + (i.1.get k).2 ≤ s₂ j) ∧
    (∀ j, s₁ j + (i.1.get j).1 ≤ s₂ j) ∧
    ∀ j, s₂ j + (i.1.get j).2 ≤ i.2

open Classical in
/-- TWO-STAGE HYBRID FLOW SHOP as a decision problem over bitstrings. -/
noncomputable def twoStageHybridFlowShopDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoStageHybridFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ TwoStageHybridFlowShopFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoStageHybridFlowShop
