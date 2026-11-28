/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEDICATED-PROCESSOR SCHEDULING `P2|chains;p_i=1;fix_i|ΣC_i`: definitions

Source:
J. A. Hoogeveen, S. L. van de Velde and B. Veltman, "Complexity of scheduling multiprocessor
tasks with prespecified processor allocations", Discrete Applied Mathematics 55 (1994),
259-272, doi:10.1016/0166-218X(94)90012-4, Theorem 3.6;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Multiprocessor task problems with dedicated processors"
(`P2|chains;p_i=1;fix_i|ΣC_i`, minimal NP-hard in the strong sense).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsTotalCompletion

open MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsMakespan
  (TwoProcessorUnitDedicatedChainsInstance WellFormed IsSchedule)

/-- Some schedule has total completion time `Σ_j (s j + 1)` at most `K`. -/
def TwoProcessorUnitDedicatedChainsTotalCompletionFeasible
    (i : TwoProcessorUnitDedicatedChainsInstance) : Prop :=
  ∃ s, IsSchedule i s ∧ (∑ j, (s j + 1)) ≤ i.1.2.2

open Classical in
/-- `P2|chains;p_i=1;fix_i|ΣC_i` as a decision problem over bitstrings. -/
noncomputable def twoProcessorUnitDedicatedChainsTotalCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorUnitDedicatedChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorUnitDedicatedChainsTotalCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitDedicatedChainsTotalCompletion
