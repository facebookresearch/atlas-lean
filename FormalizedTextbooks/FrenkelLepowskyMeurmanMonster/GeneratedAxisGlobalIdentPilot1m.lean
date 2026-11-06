/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1mPartS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1mPartX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1mPartT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1

/-! # Pilot identification: Fifth root 1, inverse triality, and both images of root 1

With `g' = q(6293364) σ(32) h₁`, `sExtra⁻¹ (h₁ v₅) = g' v₅` (the fully packed exact pairing is `128`).
Together with the positive identification (`pilot1_pos`) the coset transfer of worker `gfifth`
places both triality images at the Fifth forest root 1 in the union of the twelve local orbits. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of `sExtra⁻¹ (h₁ v₅)` with `g' v₅` is `128`. -/
theorem pilot1m_pair : pairTriPO 32 64 false pilot1Lg pilot1mW pilot1LX pilot1mWX
    ((tensorWordDenAll pilot1H : ℚ) * 1) ((tensorWordDenAll pilot1mG : ℚ) * 1) = 128 := by
  unfold pairTriPO
  rw [pilot1m_partM, pilot1m_partP, pilot1m_partO, pilot1m_partXW, pilot1m_partXL, pilot1m_partT]
  have hL : pilot1Lg.sden = 1 / 16 := rfl
  have hW : pilot1mW.sden = 1 / 16 := rfl
  have hD : tensorWordDenAll pilot1H = 256 := by decide
  have hE : tensorWordDenAll pilot1mG = 512 := by decide
  rw [hL, hW, hD, hE]
  norm_num

/-- Pilot identification, inverse triality: `sExtra⁻¹ (h₁ v₅) = g' v₅`. -/
theorem pilot1m_ident : sExtra.symm (rhoLocal (identWordLocal pilot1H)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal pilot1mG) (generatedAxisGlobalTwelveRepresentative 4) := by
  have hX := (tensorWordAll_actual pilot1H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [pilot1H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual pilot1mG (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [pilot1mG_growth]; norm_num) 1).1
  rw [pilot1H_growth] at hX
  rw [pilot1mG_growth] at hY
  exact ident_inverse_PO 4 4 _ _ pilot1Lg pilot1mW pilot1Lg_ok pilot1mW_ok pilot1_octOk rfl rfl
    hX hY pilot1m_bounds (pilot1L_actual.trans pilot1Lg_real.symm) pilot1mW_actual pilot1m_pair

/-- Fifth root 1, inverse triality: the image at the one-xi representative lies in the union of
the twelve local orbits. -/
theorem pilot1_neg :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 1) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := pilot1m_ident
  rw [pilot1H_local] at h
  have h4 : generatedAxisGlobalTwelveRepresentative 4 = generatedFifthAxis := rfl
  rw [h4] at h
  change sExtra.symm (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 1) generatedFifthAxis) ∈ _
  rw [h]
  exact generatedAxisGlobalTwelve_mem_of_transport 4 _ rfl

/-- Both triality images at the Fifth forest root 1 lie in the union of the twelve local orbits. -/
theorem fifthRoot1_covered :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 1) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalFifthShortLocalWord 1) generatedFifthAxis) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveFifthBindCoset_transfer 1 pilot1_pos pilot1_neg

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
