/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairSwitchInterface















open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropFractionalTransport (p : Prop) : Decidable p :=
  Classical.propDecidable p



structure FiniteFractionalTransport
    (Source Target : Type*) [Fintype Source] [Fintype Target]
    (sourceMass : Source -> Real) (targetCapacity : Target -> Real) where
  flow : Source -> Target -> Real
  flow_nonneg : forall source target, 0 <= flow source target
  row_sum : forall source, (∑ target, flow source target) = sourceMass source
  column_le : forall target,
    (∑ source, flow source target) <= targetCapacity target



theorem FiniteFractionalTransport.total_le
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceMass : Source -> Real} {targetCapacity : Target -> Real}
    (transport : FiniteFractionalTransport
      Source Target sourceMass targetCapacity) :
    (∑ source, sourceMass source) <= ∑ target, targetCapacity target := by
  calc
    (∑ source, sourceMass source) =
        ∑ source, ∑ target, transport.flow source target := by
      apply Finset.sum_congr rfl
      intro source hsource
      exact (transport.row_sum source).symm
    _ = ∑ target, ∑ source, transport.flow source target :=
      Finset.sum_comm
    _ <= ∑ target, targetCapacity target :=
      Finset.sum_le_sum fun target htarget => transport.column_le target


structure FiniteFractionalTransportOn
    (Source Target : Type*) [Fintype Source] [Fintype Target]
    (sourceMass : Source -> Real) (targetCapacity : Target -> Real)
    (related : Source -> Target -> Prop)
    extends FiniteFractionalTransport
      Source Target sourceMass targetCapacity where
  supported : forall source target,
    ¬ related source target -> flow source target = 0

theorem FiniteFractionalTransportOn.total_le
    {Source Target : Type*} [Fintype Source] [Fintype Target]
    {sourceMass : Source -> Real} {targetCapacity : Target -> Real}
    {related : Source -> Target -> Prop}
    (transport : FiniteFractionalTransportOn
      Source Target sourceMass targetCapacity related) :
    (∑ source, sourceMass source) <= ∑ target, targetCapacity target :=
  transport.toFiniteFractionalTransport.total_le



abbrev SixVertexMarkedPairSource
    (T : EvenTorus) (lower upper : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T lower ×
    SixVertexMarkedSectorConfiguration T upper



abbrev SixVertexMarkedPairTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle


noncomputable def sixVertexMarkedConfigurationPairMass
    {T : EvenTorus} (k : Nat)
    (pair : SixVertexArrows T × SixVertexArrows T) : Real :=
  sixVertexMarkedPairMultiplicity pair.1 pair.2 k



abbrev SixVertexMarkedPairFractionalTransport
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat) :=
  FiniteFractionalTransport
    (SixVertexMarkedPairSource T lower upper)
    (SixVertexMarkedPairTarget T middle)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)




abbrev SixVertexMarkedPairFractionalTransportOn
    (T : EvenTorus)
    (lower middle upper : Fin (T.width + 1)) (k : Nat)
    (related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop) :=
  FiniteFractionalTransportOn
    (SixVertexMarkedPairSource T lower upper)
    (SixVertexMarkedPairTarget T middle)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    (fun pair => sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k)
    related


theorem sixVertexMarkedSectorPairMass_le_of_fractionalTransport
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (transport : SixVertexMarkedPairFractionalTransport
      T lower middle upper k) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  change
    (∑ pair : SixVertexMarkedPairSource T lower upper,
      sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k) <=
    ∑ pair : SixVertexMarkedPairTarget T middle,
      sixVertexMarkedPairMultiplicity pair.1.1 pair.2.1 k
  exact transport.total_le


theorem sixVertexMarkedSectorPairMass_le_of_fractionalTransportOn
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop}
    (transport : SixVertexMarkedPairFractionalTransportOn
      T lower middle upper k related) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k :=
  sixVertexMarkedSectorPairMass_le_of_fractionalTransport
    transport.toFiniteFractionalTransport



theorem coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (transport : SixVertexMarkedPairFractionalTransport
      T lower middle upper k) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
  rw [pow_two]
  rw [← sixVertexMarkedSectorPairMass_eq_coeff,
    ← sixVertexMarkedSectorPairMass_eq_coeff]
  exact sixVertexMarkedSectorPairMass_le_of_fractionalTransport transport



theorem coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransportOn
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedPairSource T lower upper ->
      SixVertexMarkedPairTarget T middle -> Prop}
    (transport : SixVertexMarkedPairFractionalTransportOn
      T lower middle upper k related) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k :=
  coeff_shiftedSectorTrace_mul_le_sq_of_fractionalTransport
    transport.toFiniteFractionalTransport

end

end StatMech.FrontierD
