/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Σw_iC_i is NP-complete

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_tra` (open-shop problems with transportation delays), Universität Osnabrück (last
update 2006).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import WantedExt.Complexity.NPComplete.UnitFlowShopDelaysWeightedWanted
public import WantedExt.Complexity.NPComplete.UnitOpenShopTransportationDelaysWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopDelaysWeighted

open UnitOpenShopTransportationDelays (IsUnitOpenShopScheduleWithDelays)
open UnitFlowShopDelaysWeighted (UnitFlowShopDelaysWeightedInstance WellFormed)

/-!
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i|Σw_iC_i is NP-complete

INSTANCE: `n` jobs, each consisting of two unit-time operations, one on machine `M₁` and one on
machine `M₂`, which may be processed in either order but not at the same time; for each job `j`
a transportation delay `t_j ∈ ℤ₀⁺` and a weight `w_j ∈ ℤ₀⁺`; a bound `K`. Each machine
processes at most one operation at a time, and the operation of job `j` processed second cannot
start until `t_j` time units after the completion of the operation processed first (the delay
uses no machine, and any number of jobs can be in transit at once). QUESTION: is there a
schedule whose total weighted completion time `∑_j w_j C_j` is at most `K`, where `C_j` is the
completion time of job `j`'s last operation?

In the three-field notation this is `O2|p_ij=1; t_i|∑ w_i C_i`. Brucker and Knust's
classification lists it as minimal strongly NP-hard, citing Brucker, Cheng, Knust and
Shakhlevich (2004), whose survey of flow-shop and open-shop problems with transportation delays
derives new complexity results; the full text was not available to this formalization.

The instance (job `j` is the `j`-th pair `(t_j, w_j)` of delay and weight) and the well-formedness
(every such list with a bound is an instance) are those of the flow shop `F2|p_ij=1; t_j|∑ w_j C_j`
(`UnitFlowShopDelaysWeightedWanted`). A schedule is the open-shop schedule of
`UnitOpenShopTransportationDelaysWanted` (`O2|p_ij=1; t_i|C_max`):
`IsUnitOpenShopScheduleWithDelays` with the job delays, i.e. the operations on each machine, and the
two operations of each job, start at different times, and the two operations of job `j`, in either
order, are separated by at least `t_j`; `C_j = max(σ₁(j), σ₂(j)) + 1`. Start times are natural
numbers: with integer data, fixing the order of the operations on each machine and within each job,
and starting every operation as early as these orders and the delays allow, gives an integral
schedule whose completion times are no later, so this does not change the answer. Binary encoding of
all numbers (the problem is NP-complete in the strong sense).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some open-shop schedule with the job delays `t_j = (i.1.get j).1` has total weighted
completion time `∑_j w_j C_j` at most `K`, where `w_j = (i.1.get j).2` and
`C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def UnitOpenShopDelaysWeightedFeasible (i : UnitFlowShopDelaysWeightedInstance) : Prop :=
  ∃ σ : Fin 2 → Fin i.1.length → ℕ,
    IsUnitOpenShopScheduleWithDelays (fun j => (i.1.get j).1) σ ∧
    ∑ j, (i.1.get j).2 * (max (σ 0 j) (σ 1 j) + 1) ≤ i.2

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i|∑ w_i C_i` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopDelaysWeightedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopDelaysWeightedInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopDelaysWeightedFeasible i)
  | none => false

/-- **OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i|∑ w_i C_i` is NP-complete.** Source:
Brucker, Cheng, Knust and Shakhlevich (2004); Brucker and Knust, scheduling classification,
class `o_tra`. -/
public theorem_wanted unitOpenShopDelaysWeighted_npComplete :
    unitOpenShopDelaysWeightedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unitOpenShopDelaysWeightedDec

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopDelaysWeighted
