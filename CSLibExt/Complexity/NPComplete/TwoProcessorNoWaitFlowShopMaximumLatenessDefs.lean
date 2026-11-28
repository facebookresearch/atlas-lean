/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS: definitions

Source:
H. Röck, "Some new results in flow shop scheduling", Zeitschrift für Operations Research 28
(1984), 1-16, doi:10.1007/BF01919082 (`F2|no-wait|Lmax` is NP-hard in the strong sense);
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
table "Flow-shop problems with no-wait" (`F2|no-wait|Lmax`, minimal NP-hard, credited to Röck
1984);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS16] NO-WAIT FLOW-SHOP SCHEDULING,
p. 242 (the deadline version, solvable in polynomial time for `m = 2`, Gilmore and Gomory 1964).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness

/-- An instance: the jobs, job `j` being the `j`-th triple `(pⱼ₁, pⱼ₂, dⱼ)` of its processing
times on `M₁` and `M₂` and its due date, and the bound `y` as a pair `(y⁺, y⁻)` with
`y = y⁺ - y⁻`. -/
abbrev TwoProcessorNoWaitFlowShopMaximumLatenessInstance := List (ℕ × ℕ × ℕ) × (ℕ × ℕ)

/-- The jobs of the instance, `Fin n` for `n` listed triples. -/
abbrev Job (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Type := Fin i.1.length

/-- The processing time `pⱼ₁` of job `j` on machine `M₁`. -/
def time₁ (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The processing time `pⱼ₂` of job `j` on machine `M₂`. -/
def time₂ (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.1

/-- The due date `dⱼ` of job `j`. -/
def dueDate (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) (j : Job i) : ℕ :=
  (i.1.get j).2.2

/-- Every instance is well-formed: processing times and due dates are nonnegative integers by
their type, and the bound `y` is an arbitrary integer. -/
def WellFormed (_i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Prop := True

/-- Some schedule, with starting times `s₁ j` on `M₁` and `s₂ j` on `M₂`, runs one operation at
a time on each machine, starts each job on `M₂` exactly when it is completed on `M₁`, and
completes every job `j` on `M₂` with lateness `Cⱼ - dⱼ ≤ y⁺ - y⁻`. -/
def TwoProcessorNoWaitFlowShopMaximumLatenessFeasible
    (i : TwoProcessorNoWaitFlowShopMaximumLatenessInstance) : Prop :=
  ∃ s₁ s₂ : Job i → ℕ,
    (∀ j k, j ≠ k → s₁ j + time₁ i j ≤ s₁ k ∨ s₁ k + time₁ i k ≤ s₁ j) ∧
    (∀ j k, j ≠ k → s₂ j + time₂ i j ≤ s₂ k ∨ s₂ k + time₂ i k ≤ s₂ j) ∧
    (∀ j, s₂ j = s₁ j + time₁ i j) ∧
    ∀ j, s₂ j + time₂ i j + i.2.2 ≤ dueDate i j + i.2.1

open Classical in
/-- TWO-PROCESSOR NO-WAIT FLOW-SHOP MAXIMUM LATENESS as a decision problem over bitstrings. -/
noncomputable def twoProcessorNoWaitFlowShopMaximumLatenessDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorNoWaitFlowShopMaximumLatenessInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorNoWaitFlowShopMaximumLatenessFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorNoWaitFlowShopMaximumLateness
