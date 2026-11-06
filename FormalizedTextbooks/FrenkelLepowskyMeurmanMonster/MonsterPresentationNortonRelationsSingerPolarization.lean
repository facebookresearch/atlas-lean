/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The source theta cocycle is preserved by the explicit Singer permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialPolarization

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The source cocycle difference is a genuine bilinear form, with no bilinearity assumption. -/
def monsterNortonSingerThetaBilinear (k : Fin 1) :
    SpinIndex →ₗ[ZMod 2] SpinIndex →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (monsterNortonSingerThetaDifference k)
    (monsterNortonSingerThetaDifference_add_left k)
    (by
      intro c a b
      have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
      obtain rfl | rfl := hc c <;> simp [monsterNortonSingerThetaDifference])
    (monsterNortonSingerThetaDifference_add_right k)
    (by
      intro c a b
      have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
      obtain rfl | rfl := hc c <;> simp [monsterNortonSingerThetaDifference])

/-- Evaluation of the bundled source bilinear form retains the defining cocycle difference. -/
theorem monsterNortonSingerThetaBilinear_apply (k : Fin 1) (a b : SpinIndex) :
    monsterNortonSingerThetaBilinear k a b =
      monsterNortonSingerThetaDifference k a b := rfl

set_option maxHeartbeats 4000000 in
-- Check the 144 basis values of the actual bilinear forms before linear extension.
/-- The concrete triangular quadratic phase has exactly the required source polarization. -/
theorem monsterNortonSingerTheta_basis_certificate : ∀ k i j,
    monsterNortonSingerThetaDifference k (Pi.single i 1) (Pi.single j 1) =
      spinDot (monsterMonomialGradient (monsterNortonSingerPhaseMatrix k)
        (Pi.single i 1)) (Pi.single j 1) := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Bilinear extension proves the source identity on every pair of codewords. -/
theorem monsterNortonSingerTheta_bilinear (k : Fin 1) :
    monsterNortonSingerThetaBilinear k =
      monsterMonomialGradientBilinear (monsterNortonSingerPhaseMatrix k) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro j
  simp only [Pi.basisFun_apply, monsterNortonSingerThetaBilinear_apply]
  exact (monsterNortonSingerTheta_basis_certificate k i j).trans
    (monsterMonomialGradientBilinear_apply (monsterNortonSingerPhaseMatrix k)
      (Pi.single i 1) (Pi.single j 1)).symm

/-- The checked phase satisfies Seysen's defining Parker automorphism equation for all codes. -/
theorem monsterNortonSingerPhase_polarization (k : Fin 1) (a b : SpinIndex) :
    monsterNortonSingerPhase k (a + b) = monsterNortonSingerPhase k a +
      monsterNortonSingerPhase k b +
        monsterNortonSingerThetaDifference k a b := by
  have h := LinearMap.congr_fun₂ (monsterNortonSingerTheta_bilinear k) a b
  have hd := (monsterNortonSingerThetaBilinear_apply k a b).symm.trans
    (h.trans (monsterMonomialGradientBilinear_apply (monsterNortonSingerPhaseMatrix k) a b))
  rw [hd]
  exact monsterMonomialQuadratic_add (monsterNortonSingerPhaseMatrix k) a b

/-- This physical permutation’s source Parker phase is identically zero. -/
theorem monsterNortonSingerPhase_zero (k : Fin 1) (a : SpinIndex) :
    monsterNortonSingerPhase k a = 0 := by
  have hm : monsterNortonSingerPhaseMatrix k = 0 := by
    funext i j
    have hr : ∀ k i, monsterNortonSingerPhaseRows k i = 0 := by decide +kernel
    rw [monsterNortonSingerPhase_certificate, hr, Nat.zero_testBit]
    rfl
  simp [monsterNortonSingerPhase, hm]

/-- The actual theta cocycle is preserved on every pair of source codewords. -/
theorem monsterNortonSingerThetaDifference_zero (k : Fin 1) (a b : SpinIndex) :
    monsterNortonSingerThetaDifference k a b = 0 := by
  have h := monsterNortonSingerPhase_polarization k a b
  simpa only [monsterNortonSingerPhase_zero, zero_add] using h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
