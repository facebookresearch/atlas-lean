/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The standard Parker phases satisfy the full cocycle law on all codewords. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialPhase

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The derivative of a concrete binary quadratic sign is a genuine linear map. -/
def monsterMonomialGradientLinear (M : Fin 12 → Fin 12 → ZMod 2) :
    SpinIndex →ₗ[ZMod 2] SpinIndex where
  toFun := monsterMonomialGradient M
  map_add' a b := by
    ext j
    simp [monsterMonomialGradient, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext j
    simp [monsterMonomialGradient, mul_assoc, Finset.mul_sum]

/-- The polarization of the actual quadratic sign, as a genuine bilinear form. -/
def monsterMonomialGradientBilinear (M : Fin 12 → Fin 12 → ZMod 2) :
    SpinIndex →ₗ[ZMod 2] SpinIndex →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun a b => spinDot (monsterMonomialGradient M a) b)
    (by
      intro a b c
      change spinDot (monsterMonomialGradientLinear M (a + b)) c = _
      rw [map_add, spinDot_add_left]
      rfl)
    (by
      intro c a b
      change spinDot (monsterMonomialGradientLinear M (c • a)) b = _
      rw [map_smul, xiSpinDot_smul_left]
      rfl)
    (by intro a b c; exact spinDot_add_right _ _ _)
    (by intro c a b; exact xiSpinDot_smul_right _ _ _)

/-- The source cocycle difference is a genuine bilinear form, with no bilinearity assumption. -/
def monsterSourcePermutationThetaBilinear (k : Fin 2) :
    SpinIndex →ₗ[ZMod 2] SpinIndex →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (monsterSourcePermutationThetaDifference k)
    (monsterSourcePermutationThetaDifference_add_left k)
    (by
      intro c a b
      have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
      obtain rfl | rfl := hc c <;> simp [monsterSourcePermutationThetaDifference])
    (monsterSourcePermutationThetaDifference_add_right k)
    (by
      intro c a b
      have hc : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
      obtain rfl | rfl := hc c <;> simp [monsterSourcePermutationThetaDifference])

/-- Evaluation of the bundled source bilinear form retains the defining cocycle difference. -/
theorem monsterSourcePermutationThetaBilinear_apply (k : Fin 2) (a b : SpinIndex) :
    monsterSourcePermutationThetaBilinear k a b =
      monsterSourcePermutationThetaDifference k a b := rfl

/-- Evaluation of the bundled gradient form retains the actual quadratic derivative. -/
theorem monsterMonomialGradientBilinear_apply (M : Fin 12 → Fin 12 → ZMod 2)
    (a b : SpinIndex) : monsterMonomialGradientBilinear M a b =
      spinDot (monsterMonomialGradient M a) b := rfl

set_option maxHeartbeats 4000000 in
-- Check the 288 basis values of the actual bilinear forms before linear extension.
/-- The concrete triangular quadratic phase has exactly the required source polarization. -/
theorem monsterSourcePermutationTheta_basis_certificate : ∀ k i j,
    monsterSourcePermutationThetaDifference k (Pi.single i 1) (Pi.single j 1) =
      spinDot (monsterMonomialGradient (monsterSourcePermutationPhaseMatrix k)
        (Pi.single i 1)) (Pi.single j 1) := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Bilinear extension proves the source identity on every pair of codewords. -/
theorem monsterSourcePermutationTheta_bilinear (k : Fin 2) :
    monsterSourcePermutationThetaBilinear k =
      monsterMonomialGradientBilinear (monsterSourcePermutationPhaseMatrix k) := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro j
  simp only [Pi.basisFun_apply, monsterSourcePermutationThetaBilinear_apply]
  exact (monsterSourcePermutationTheta_basis_certificate k i j).trans
    (monsterMonomialGradientBilinear_apply (monsterSourcePermutationPhaseMatrix k)
      (Pi.single i 1) (Pi.single j 1)).symm

/-- The checked phase satisfies Seysen's defining Parker automorphism equation for all codes. -/
theorem monsterSourcePermutationPhase_polarization (k : Fin 2) (a b : SpinIndex) :
    monsterSourcePermutationPhase k (a + b) = monsterSourcePermutationPhase k a +
      monsterSourcePermutationPhase k b +
        monsterSourcePermutationThetaDifference k a b := by
  have h := LinearMap.congr_fun₂ (monsterSourcePermutationTheta_bilinear k) a b
  have hd := (monsterSourcePermutationThetaBilinear_apply k a b).symm.trans
    (h.trans (monsterMonomialGradientBilinear_apply (monsterSourcePermutationPhaseMatrix k) a b))
  rw [hd]
  exact monsterMonomialQuadratic_add (monsterSourcePermutationPhaseMatrix k) a b

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
