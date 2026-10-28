/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1PartS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1PartX
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1PartT

/-! # Pilot identification: Fifth root 1, positive triality

With `h₁ = xi⁻¹ P₀ P₁⁻¹ P₀⁻¹ P₁⁻¹` (the one-xi representative of Fifth root 1, worker `gfifth`)
and `g = q(4073160) σ(1024) h₁`, the triality image `sExtra (h₁ v₅)` of the Fifth axis is `g v₅`:
the fully packed exact pairing `pairTriPO` of the two representations is `128`, assembled from
its separately checked parts (matrix `3`, pairs `0`, octads, odd cross terms, tensor part). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The exact pairing of `sExtra (h₁ v₅)` with `g v₅` is `128`. -/
theorem pilot1_pair : pairTriPO 32 64 true pilot1Lg pilot1W pilot1LX pilot1WX
    ((tensorWordDenAll pilot1H : ℚ) * 1) ((tensorWordDenAll pilot1G : ℚ) * 1) = 128 := by
  unfold pairTriPO
  rw [pilot1_partM, pilot1_partP, pilot1_partO, pilot1_partXW, pilot1_partXL, pilot1_partT]
  have hL : pilot1Lg.sden = 1 / 16 := rfl
  have hW : pilot1W.sden = 1 / 16 := rfl
  have hD : tensorWordDenAll pilot1H = 256 := by decide
  have hE : tensorWordDenAll pilot1G = 512 := by decide
  rw [hL, hW, hD, hE]
  norm_num

/-- Pilot identification: `sExtra (h₁ v₅) = g v₅`. -/
theorem pilot1_ident : sExtra (rhoLocal (identWordLocal pilot1H)
    (generatedAxisGlobalTwelveRepresentative 4)) =
      rhoLocal (identWordLocal pilot1G) (generatedAxisGlobalTwelveRepresentative 4) := by
  have hX := (tensorWordAll_actual pilot1H (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [pilot1H_growth]; norm_num) 1).1
  have hY := (tensorWordAll_actual pilot1G (fifthSrcXW_bnd (w := 64) (by norm_num))
    (by rw [pilot1G_growth]; norm_num) 1).1
  rw [pilot1H_growth] at hX
  rw [pilot1G_growth] at hY
  exact ident_forward_PO 4 4 _ _ pilot1Lg pilot1W pilot1Lg_ok pilot1W_ok pilot1_octOk rfl rfl
    hX hY pilot1_bounds (pilot1L_actual.trans pilot1Lg_real.symm) pilot1W_actual pilot1_pair

/-- The source word is the one-xi representative of Fifth root 1. -/
theorem pilot1H_local : identWordLocal pilot1H = generatedAxisGlobalTwelveFifthBindCoset 1 := by
  have h1 : identWordFiber pilot1H = xiSpinLocalFiber * (xiSpinLocalFiber *
      (generatedFourthMonomialFiberLetter (0, false) * (generatedFourthMonomialFiberLetter (1, true) *
        (generatedFourthMonomialFiberLetter (0, true) * generatedFourthMonomialFiberLetter (1, true))))) := by
    simp only [identWordFiber, pilot1H, pilot1Wh, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rfl
  have h2 : generatedAxisGlobalTwelveFifthBindCosetFiber 1 = xiSpinLocalFiber⁻¹ *
      monsterSourcePermutationFiber 0 * (monsterSourcePermutationFiber 1)⁻¹ *
        (monsterSourcePermutationFiber 0)⁻¹ * (monsterSourcePermutationFiber 1)⁻¹ := rfl
  rw [identWordLocal, generatedAxisGlobalTwelveFifthBindCoset, h1, h2]
  simp only [generatedFourthMonomialFiberLetter, Bool.false_eq_true, ↓reduceIte, xiFiber_inv,
    mul_assoc]

/-- Fifth root 1, positive triality: the image at the one-xi representative lies in the union of
the twelve local orbits. -/
theorem pilot1_pos :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFifthBindCoset 1) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  have h := pilot1_ident
  rw [pilot1H_local] at h
  have h4 : generatedAxisGlobalTwelveRepresentative 4 = generatedFifthAxis := rfl
  rw [h4] at h
  rw [h]
  exact generatedAxisGlobalTwelve_mem_of_transport 4 _ rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
