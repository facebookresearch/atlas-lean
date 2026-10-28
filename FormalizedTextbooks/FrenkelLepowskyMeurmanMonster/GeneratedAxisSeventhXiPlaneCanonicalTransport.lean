/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalMiddle
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSourceSignLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhProjection

/-! Checked spin-sign transport retains the genuine local quotient and Conway projection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- The final canonical vector is positive triality applied to the normalized middle axis. -/
def generatedSeventhXiPlaneCanonicalAxis : GriessSpace :=
  sExtra generatedSeventhXiPlaneCanonicalMiddle

/-- The genuine Pauli element encoding the other triality-transported central sign. -/
def generatedSeventhXiPlaneSignCorrection : Q := qCentralInvolution * sourceOmegaQ

/-- This actual Q element is precisely the positive triality conjugate of the central involution. -/
theorem generatedSeventhXiPlaneSignCorrection_action :
    rhoLocal (inclQ generatedSeventhXiPlaneSignCorrection) =
      sExtra * localCentralGriess * sExtra⁻¹ := by
  have ho := congrArg Subtype.val qIntoGenerated_sourceOmegaQ
  change rhoLocal (inclQ sourceOmegaQ) = trialityCentralSign 2 at ho
  have h := localCentralGriess_mul_conjugate
  rw [localCentralGriess_conjugate_square] at h
  have hz : localCentralGriess * localCentralGriess = 1 := by
    rw [localCentralGriess_eq_trialityCentralSign]
    exact trialityCentralSign_square 0
  rw [generatedSeventhXiPlaneSignCorrection, map_mul, map_mul, ho]
  change localCentralGriess * trialityCentralSign 2 = _
  rw [← h, ← mul_assoc, hz, one_mul]

/-- The full actual axis is Q-conjugate to the canonical sign by an explicit Pauli choice. -/
theorem generatedSeventhXi_canonical_axis_correction :
    ∃ q : Q, (q = 1 ∨ q = generatedSeventhXiPlaneSignCorrection) ∧
      generatedSeventhAxis = rhoLocal (inclQ q) generatedSeventhXiPlaneCanonicalAxis := by
  rcases generatedSeventhXi_middle_canonical_sign with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [map_one, map_one]
    change generatedSeventhAxis = sExtra generatedSeventhXiPlaneCanonicalMiddle
    exact generatedSeventhAxis_local_expression.trans (congrArg sExtra h)
  · refine ⟨generatedSeventhXiPlaneSignCorrection, Or.inr rfl, ?_⟩
    rw [generatedSeventhXiPlaneSignCorrection_action]
    change generatedSeventhAxis =
      sExtra (localCentralGriess (sExtra.symm (sExtra generatedSeventhXiPlaneCanonicalMiddle)))
    rw [LinearEquiv.symm_apply_apply]
    exact generatedSeventhAxis_local_expression.trans (congrArg sExtra h)

/-- Every complete canonical-axis fixer projects into the actual axis stabilizer. -/
theorem generatedSeventhXi_canonical_fixer_projected (h : H)
    (hh : rhoLocal h generatedSeventhXiPlaneCanonicalAxis = generatedSeventhXiPlaneCanonicalAxis) :
    projH h ∈ generatedSeventhProjectedAxisStabilizer := by
  obtain ⟨q, _, hq⟩ := generatedSeventhXi_canonical_axis_correction
  let k : H := inclQ q * h * (inclQ q)⁻¹
  have hk : k ∈ generatedSeventhLocalAxisStabilizer := by
    change rhoLocal k generatedSeventhAxis = generatedSeventhAxis
    rw [hq]
    simp only [k, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
    rw [LinearEquiv.symm_apply_apply, hh]
  have hp : projH k = projH h := by
    simp only [k, map_mul, map_inv, projH_inclQ, one_mul, inv_one, mul_one]
  exact ⟨⟨k, hk⟩, hp⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
