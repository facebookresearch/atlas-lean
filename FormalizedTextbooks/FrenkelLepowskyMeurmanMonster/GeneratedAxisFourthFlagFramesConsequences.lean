/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthFlagFramesGeneration
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthQOrbitCount

/-! Full fourth-axis stabilizer and physical matrix fiber after actual flag generation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual full axes in the fourth H orbit sharing the original physical matrix. -/
def generatedFourthMatrixFiber : Set GriessSpace :=
  {x | x ∈ MulAction.orbit H generatedFourthAxis ∧
    (griessConwayEncode x).1 = (griessConwayEncode generatedFourthAxis).1}

/-- Full flag generation determines the entire genuine H stabilizer order. -/
theorem generatedFourthFlagFrames_local_stabilizer_card
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort) :
    Nat.card generatedFourthLocalAxisStabilizer = 95126814720 := by
  have hr : generatedFourthProjectedAxisStabilizer = ⊤ :=
    MonoidHom.range_eq_top.mpr (generatedFourthFlagGenerator_projection_surjective hgen)
  rw [generatedFourth_local_stabilizer_card_range, hr, Subgroup.card_top,
    generatedAxisE8Co1ShortFlagStabilizer_card _ _ generatedFourth_flag_incident]

/-- Every local element over the physical flag differs from an axis-fixing lift by Q. -/
theorem generatedFourthFlagFrames_phase_factorization
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort)
    (h : H) (hp : projH h ∈ generatedAxisE8Co1ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort) :
    ∃ q : Q, rhoLocal (inclQ q) generatedFourthAxis = rhoLocal h generatedFourthAxis := by
  obtain ⟨k, hk⟩ := generatedFourthFlagGenerator_projection_surjective hgen ⟨projH h, hp⟩
  have he : projH k.val = projH h := congrArg Subtype.val hk
  have hker : h * k.val⁻¹ ∈ projH.ker := by
    change projH (h * k.val⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [← inclQ_range_eq_projH_ker] at hker
  obtain ⟨q, hq⟩ := hker
  have hfix : k.val⁻¹ • generatedFourthAxis = generatedFourthAxis := by
    rw [inv_smul_eq_iff]
    exact k.property.symm
  refine ⟨q, ?_⟩
  rw [hq]
  change (h * k.val⁻¹) • generatedFourthAxis = h • generatedFourthAxis
  rw [mul_smul, hfix]

/-- The physical matrix fiber equals the genuine full-axis Q orbit after full flag generation. -/
theorem generatedFourthFlagFrames_matrix_fiber_eq
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort) :
    generatedFourthMatrixFiber = generatedFourthQAxisOrbit := by
  ext x
  constructor
  · rintro ⟨⟨h, hh⟩, hmatrix⟩
    change h • generatedFourthAxis = x at hh
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
    change localFiberIntoH f = h at hf
    have hm : (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedFourthAxis)).1 =
        (griessConwayEncode generatedFourthAxis).1 := by
      rw [hf]
      change (griessConwayEncode (h • generatedFourthAxis)).1 = _
      rw [hh]
      exact hmatrix
    change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at hm
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hm
    have hg := generatedFourth_matrix_stabilizer_iff f.val.2 |>.mp hm
    have hp : projH h ∈ generatedAxisE8Co1ShortFlagStabilizer
        generatedFourthFlagOctad generatedFourthFlagShort := by
      refine ⟨f.val.2, hg, ?_⟩
      change QuotientGroup.mk' signsSubgroup f.val.2 = projH h
      rw [← hf]
      rfl
    obtain ⟨q, hq⟩ := generatedFourthFlagFrames_phase_factorization hgen h hp
    exact ⟨q, hq.trans hh⟩
  · rintro ⟨q, rfl⟩
    refine ⟨⟨inclQ q, rfl⟩, ?_⟩
    change (griessConwayEncode
      (localGriessRepresentation (localFiberIncl q) generatedFourthAxis)).1 = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl

/-- The genuine fourth matrix fiber has exactly 262144 full axes after flag generation. -/
theorem generatedFourthFlagFrames_matrix_fiber_card
    (hgen : generatedFourthPhysicalFlagGeneratorSubgroup =
      generatedAxisE8ShortFlagStabilizer generatedFourthFlagOctad generatedFourthFlagShort) :
    Nat.card generatedFourthMatrixFiber = 262144 := by
  rw [generatedFourthFlagFrames_matrix_fiber_eq hgen, generatedFourth_q_axis_orbit_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
