/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The actual local group centralizes its distinguished central involution.
This is the inclusion into the 2B centralizer; it does not assert equality
with the full centralizer in the generated group.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityKleinFour
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedSubgroups
public import Mathlib.GroupTheory.Subgroup.Centralizer

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem localGriessRepresentation_commute_central (f : localFiberSubgroup) :
    localGriessRepresentation f * localCentralGriess =
      localCentralGriess * localGriessRepresentation f := by
  apply LinearEquiv.ext
  intro x
  have he : griessConwayEncode (localGriessRepresentation f (localCentralGriess x)) =
      griessConwayEncode (localCentralGriess (localGriessRepresentation f x)) := by
    rw [localGriessRepresentation_encode, localCentralGriess_encode,
      localCentralGriess_encode, localGriessRepresentation_encode,
      localConwayRawRepresentation_apply, localConwayRawRepresentation_apply]
    rw [map_neg]
  have hd := congrArg griessConwayDecode he
  simpa only [griessConwayDecode_encode, LinearEquiv.mul_apply] using hd

/-- Every element of the genuine quotient local group commutes with its actual central image. -/
theorem rhoLocal_commute_localCentralGriess (h : H) :
    rhoLocal h * localCentralGriess = localCentralGriess * rhoLocal h := by
  refine Quotient.inductionOn h ?_
  intro f
  exact localGriessRepresentation_commute_central f

/-- The genuine local image is contained in the ambient centralizer of the actual involution. -/
theorem rhoLocal_range_le_centralizer :
    rhoLocal.range ≤ Subgroup.centralizer {localCentralGriess} := by
  rintro g ⟨h, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (rhoLocal_commute_localCentralGriess h)

/-- Inside the generated group, the genuine local image centralizes the embedded Q involution. -/
theorem localIntoGenerated_commute_central (h : H) :
    localIntoGenerated h * qIntoGenerated qCentralInvolution =
      qIntoGenerated qCentralInvolution * localIntoGenerated h := by
  apply Subtype.ext
  exact rhoLocal_commute_localCentralGriess h

/-- The embedded local group lies in the actual generated-group centralizer. -/
theorem localIntoGenerated_range_le_centralizer :
    localIntoGenerated.range ≤ Subgroup.centralizer {qIntoGenerated qCentralInvolution} := by
  rintro g ⟨h, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (localIntoGenerated_commute_central h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
