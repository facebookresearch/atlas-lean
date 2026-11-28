/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM OPEN SHOP WITH THREE MACHINES (OMPM3||C_max): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS14] OPEN-SHOP SCHEDULING, comment: remains
NP-complete if `m = 3`; T. Gonzalez and S. Sahni, "Open shop scheduling to minimize finish time",
Journal of the ACM 23 (1976), 665-679, doi:10.1145/321978.321985; P. Brucker, *Scheduling
Algorithms*, 5th ed., Springer (2007), doi:10.1007/978-3-540-69516-5, Chapter 10 (the MPM open-shop
model); P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `OMPM3||C_max` as minimal NP-hard (in the ordinary sense), citing Gonzalez
and Sahni (1976).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MPMFlowShopThreeMachinesDefs
public import CSLibExt.Complexity.NPComplete.MultipurposeOpenShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MPMOpenShopThreeMachines

open MPMFlowShopThreeMachines (MPMFlowShopInstance WellFormed)
open MultipurposeFlowShopPrecedenceMakespan (completionTime)
open MultipurposeOpenShopPrecedenceMakespan (IsMPMOpenShopSchedule)

/-- Some MPM open-shop schedule on the three machines (`σ` start times, `a` machines, operation
`(j, s)` of length `p_js`) completes every job by `K`. -/
def MPMOpenShopThreeMachinesFeasible (i : MPMFlowShopInstance) : Prop :=
  ∃ σ : Fin i.1.2.1.length → Fin i.2.length → ℕ, ∃ a : Fin i.1.2.1.length → Fin i.2.length → Fin 3,
    IsMPMOpenShopSchedule 3 i.2 (fun j s => (i.1.2.1.get j).getD s 0) σ a ∧
      ∀ j, completionTime (fun j s => (i.1.2.1.get j).getD s 0) σ j ≤ i.1.2.2

open Classical in
/-- `OMPM3||C_max` as a decision problem over bitstrings. -/
noncomputable def mpmOpenShopThreeMachinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MPMFlowShopInstance) x with
  | some i => decide (WellFormed i ∧ MPMOpenShopThreeMachinesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MPMOpenShopThreeMachines
