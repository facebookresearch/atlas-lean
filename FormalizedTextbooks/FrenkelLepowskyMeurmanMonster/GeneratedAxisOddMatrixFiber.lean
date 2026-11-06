/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddQOrbitCount

/-! The actual odd-image physical matrix fiber is the full 8192-axis Q phase orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine local-axis points sharing the original odd-image physical matrix. -/
def generatedOddMatrixFiber : Set GriessSpace :=
  {x | x ∈ MulAction.orbit H generatedOddAxis ∧
    (griessConwayEncode x).1 = (griessConwayEncode generatedOddAxis).1}

/-- Every genuine H element over the line stabilizer differs from an axis-fixing lift by Q. -/
theorem generatedOdd_projected_phase_factorization (h : H)
    (hp : projH h ∈ generatedNormEightCo1LineStabilizer) :
    ∃ q : Q, rhoLocal (inclQ q) generatedOddAxis = rhoLocal h generatedOddAxis := by
  obtain ⟨k, hk⟩ := generatedOddLocalAxisProjection_surjective ⟨projH h, hp⟩
  have he : projH k.val = projH h := congrArg Subtype.val hk
  have hker : h * k.val⁻¹ ∈ projH.ker := by
    change projH (h * k.val⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [← inclQ_range_eq_projH_ker] at hker
  obtain ⟨q, hq⟩ := hker
  have hfix : k.val⁻¹ • generatedOddAxis = generatedOddAxis := by
    rw [inv_smul_eq_iff]
    exact k.property.symm
  refine ⟨q, ?_⟩
  rw [hq]
  change (h * k.val⁻¹) • generatedOddAxis = h • generatedOddAxis
  rw [mul_smul, hfix]

/-- The full actual H-orbit matrix fiber consists precisely of its genuine Q phase orbit. -/
theorem generatedOddMatrixFiber_eq_phase_orbit :
    generatedOddMatrixFiber = generatedOddQAxisOrbit := by
  ext x
  constructor
  · rintro ⟨⟨h, hh⟩, hmatrix⟩
    change h • generatedOddAxis = x at hh
    obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
    change localFiberIntoH f = h at hf
    have hm : (griessConwayEncode (rhoLocal (localFiberIntoH f) generatedOddAxis)).1 =
        (griessConwayEncode generatedOddAxis).1 := by
      rw [hf]
      change (griessConwayEncode (h • generatedOddAxis)).1 = _
      rw [hh]
      exact hmatrix
    change (griessConwayEncode (localGriessRepresentation f _)).1 = _ at hm
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hm
    have hg : f.val.2 ∈ generatedNormEightLineStabilizer :=
      (generatedNormEightLine_odd_stabilizer_iff f.val.2 0 0).mp hm
    have hp : projH h ∈ generatedNormEightCo1LineStabilizer := by
      refine ⟨f.val.2, hg, ?_⟩
      change QuotientGroup.mk' signsSubgroup f.val.2 = projH h
      rw [← hf]
      rfl
    obtain ⟨q, hq⟩ := generatedOdd_projected_phase_factorization h hp
    exact ⟨q, hq.trans hh⟩
  · rintro ⟨q, rfl⟩
    refine ⟨⟨inclQ q, rfl⟩, ?_⟩
    change (griessConwayEncode
      (localGriessRepresentation (localFiberIncl q) generatedOddAxis)).1 = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl

/-- Exactly 8192 actual full axes in the third H orbit have this physical matrix. -/
theorem generatedOddMatrixFiber_card : Nat.card generatedOddMatrixFiber = 8192 := by
  rw [generatedOddMatrixFiber_eq_phase_orbit, generatedOddQAxisOrbit_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
