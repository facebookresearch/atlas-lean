/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FLOW SHOP WITH TRANSPORTATION DELAYS F2|p_ij=1;t_i;r_i|ΣC_i: definitions

Source:
P. Brucker, T. C. E. Cheng, S. Knust and N. V. Shakhlevich, "Complexity results for flow-shop
and open-shop scheduling problems with transportation delays", Annals of Operations Research
129 (2004), 81-106, doi:10.1023/B:ANOR.0000030683.64615.c8;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, online classification,
class `f_tra` (flow-shop problems with transportation delays), Universität Osnabrück (last
update 2006).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import CSLibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimes

open UnitFlowShopTransportationDelays (IsUnitFlowShopSchedule)

/-- An instance: the jobs, job `j` being the `j`-th pair `(r_j, t_j)` of release date and
delay, and the bound `K`. -/
abbrev UnitFlowShopTransportationDelaysReleaseTimesInstance := List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` listed pairs. -/
abbrev Job (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Type :=
  Fin i.1.length

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) (j : Job i) : ℕ :=
  (i.1.get j).1

/-- The delay `t_j` of job `j`. -/
def delay (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) (j : Job i) : ℕ :=
  (i.1.get j).2

/-- Well-formedness of an instance: every list of pairs with a bound is an instance (release
dates and delays are non-negative integers, and the bound needs no condition). -/
def WellFormed (_i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  True

/-- Some schedule with the job delays starts every job no earlier than its release date and
has total completion time `∑_j C_j` at most `K`, where `C_j = σ 1 j + 1`. -/
def UnitFlowShopTransportationDelaysReleaseTimesFeasible
    (i : UnitFlowShopTransportationDelaysReleaseTimesInstance) : Prop :=
  ∃ σ : Fin 2 → Job i → ℕ, IsUnitFlowShopSchedule (delay i) σ ∧
    (∀ j, releaseDate i j ≤ σ 0 j) ∧
    ∑ j, (σ 1 j + 1) ≤ i.2

open Classical in
/-- FLOW SHOP WITH TRANSPORTATION DELAYS `F2|p_ij=1;t_i;r_i|∑ C_i` as a decision problem over
bitstrings. -/
noncomputable def unitFlowShopTransportationDelaysReleaseTimesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnitFlowShopTransportationDelaysReleaseTimesInstance) x with
  | some i => decide (WellFormed i ∧ UnitFlowShopTransportationDelaysReleaseTimesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnitFlowShopTransportationDelaysReleaseTimes
