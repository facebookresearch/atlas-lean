/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME (O2||ΣC_i): definitions

Source:
J. O. Achugbue and F. Y. Chin, "Scheduling the open shop to minimize mean flow time", SIAM
Journal on Computing 11 (1982), 709-720, doi:10.1137/0211058;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_nop` (open-shop problems without preemption), Universität Osnabrück (last update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMeanFlowTime

open OpenShopScheduling (OpenShopSchedulingInstance)
open NoWaitFlowShopScheduling (IsOpenShopSchedule taskLength)

/-- Well-formedness of an instance: two processors, every job consists of two tasks, and there
is at least one job. -/
def WellFormed (i : OpenShopSchedulingInstance) : Prop :=
  i.1 = 2 ∧ (∀ job ∈ i.2.1, job.length = i.1) ∧ 0 < i.2.1.length

/-- Some open-shop schedule `σ p j` (start of job `j`'s task on processor `p`), with every task
ending by `K`, has total completion time `∑_j max_p (σ p j + l(t_p[j]))` at most `K`. -/
def TwoProcessorOpenShopMeanFlowTimeFeasible (i : OpenShopSchedulingInstance) : Prop :=
  ∃ σ : Fin i.1 → Fin i.2.1.length → ℕ, IsOpenShopSchedule i σ ∧
    ∑ j, Finset.univ.sup (fun p => σ p j + taskLength i p j) ≤ i.2.2

open Classical in
/-- TWO-PROCESSOR OPEN-SHOP MEAN FLOW TIME `O2||∑ C_i` as a decision problem over
bitstrings. -/
noncomputable def twoProcessorOpenShopMeanFlowTimeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenShopSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopMeanFlowTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopMeanFlowTime
