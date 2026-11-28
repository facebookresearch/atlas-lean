/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP WITH TRANSPORTATION DELAYS O2|p_ij=1;t_i;r_i|ΣC_i: definitions

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `o_tra` (open-shop problems with transportation delays), Universität Osnabrück (last
update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimesDefs
public import CSLibExt.Complexity.NPComplete.UnitOpenShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelaysReleaseTimes

open UnitOpenShopTransportationDelays (IsUnitOpenShopScheduleWithDelays)
open UnitFlowShopTransportationDelaysReleaseTimes
  (UnitFlowShopTransportationDelaysReleaseTimesInstance Job releaseDate delay WellFormed)

/-- Some open-shop schedule with the job delays starts both operations of every job no earlier
than its release date and has total completion time `∑_j C_j` at most `K`, where
`C_j = max (σ 0 j) (σ 1 j) + 1`. -/
def UnitOpenShopTransportationDelaysReleaseTimesFeasible
    (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitOpenShopScheduleWithDelays (delay i) σ ∧
    (∀ m j, releaseDate i j ≤ σ m j) ∧
    ∑ j, (max (σ 0 j) (σ 1 j) + 1) ≤ i.2

open Classical in
/-- OPEN SHOP WITH TRANSPORTATION DELAYS `O2|p_ij=1;t_i;r_i|∑ C_i` as a decision problem over
bitstrings. -/
noncomputable def unitOpenShopTransportationDelaysReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ UnitOpenShopTransportationDelaysReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitOpenShopTransportationDelaysReleaseTimes
