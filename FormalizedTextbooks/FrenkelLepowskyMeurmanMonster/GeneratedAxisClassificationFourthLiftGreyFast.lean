/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSpinKernel

/-! Sparse evaluation of the exact genuine Gaussian coordinate coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual grey recovery is a binary linear map. -/
def generatedFourthLiftGreyRecoveryLin : SpinIndex →ₗ[ZMod 2] XiGrayIndex where
  toFun := generatedFourthLiftGreyRecovery
  map_add' a b := by
    ext i
    simp only [generatedFourthLiftGreyRecovery, xiGrayDual, spinDot, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, add_mul]
  map_smul' c a := by
    ext i
    simp [generatedFourthLiftGreyRecovery, xiGrayDual, spinDot, Finset.mul_sum,
      mul_left_comm]

/-- The grey projection retains exactly coordinates zero through three, ten and eleven. -/
def generatedFourthLiftGreyMask : SpinIndex →ₗ[ZMod 2] SpinIndex where
  toFun w i := if 4 ≤ i.val ∧ i.val < 10 then 0 else w i
  map_add' a b := by
    ext i
    change (if 4 ≤ i.val ∧ i.val < 10 then 0 else a i + b i) =
      (if 4 ≤ i.val ∧ i.val < 10 then 0 else a i) +
        (if 4 ≤ i.val ∧ i.val < 10 then 0 else b i)
    split_ifs <;> ring
  map_smul' c a := by
    ext i
    change (if 4 ≤ i.val ∧ i.val < 10 then 0 else c * a i) =
      c * (if 4 ≤ i.val ∧ i.val < 10 then 0 else a i)
    split_ifs <;> ring

/-- Twelve actual binary basis columns certify this exact projection formula. -/
theorem generatedFourth_lift_grey_projection :
    xiGrayCode.comp generatedFourthLiftGreyRecoveryLin = generatedFourthLiftGreyMask := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply, LinearMap.comp_apply]
  fin_cases i <;> decide +kernel

/-- The single possible coefficient is zero off the actual grey coordinate subspace. -/
def generatedFourthLiftGreyKernelFast (w : SpinIndex) : ℤ :=
  if w 4 = 0 ∧ w 5 = 0 ∧ w 6 = 0 ∧ w 7 = 0 ∧ w 8 = 0 ∧ w 9 = 0 then
    generatedFourthLiftIntSign (generatedFourthLiftGammaPhaseFast w) else 0

/-- Sparse evaluation agrees with the exact recovered actual Gaussian coefficient. -/
theorem generatedFourth_lift_grey_kernel_fast (w : SpinIndex) :
    generatedFourthLiftGreyKernel w = generatedFourthLiftGreyKernelFast w := by
  have hp := LinearMap.congr_fun generatedFourth_lift_grey_projection w
  change xiGrayCode (generatedFourthLiftGreyRecovery w) = generatedFourthLiftGreyMask w at hp
  have he : xiGrayCode (generatedFourthLiftGreyRecovery w) = w ↔
      w 4 = 0 ∧ w 5 = 0 ∧ w 6 = 0 ∧ w 7 = 0 ∧ w 8 = 0 ∧ w 9 = 0 := by
    rw [hp]
    constructor
    · intro h
      have hh (i : Fin 12) := congrFun h i
      exact ⟨(hh 4).symm, (hh 5).symm, (hh 6).symm,
        (hh 7).symm, (hh 8).symm, (hh 9).symm⟩
    · rintro ⟨h4, h5, h6, h7, h8, h9⟩
      ext i
      fin_cases i <;> simp [generatedFourthLiftGreyMask, h4, h5, h6, h7, h8, h9]
  have hs : xiGraySign (generatedFourthLiftGreyRecovery w) =
      generatedFourthLiftIntSign (generatedFourthLiftGammaPhaseFast w) := by
    unfold xiGraySign generatedFourthLiftIntSign
    rw [show xiGrayQuadratic (generatedFourthLiftGreyRecovery w) =
        generatedFourthLiftGammaPhaseFast w from generatedFourth_lift_gamma_phase_fast w]
  simp only [generatedFourthLiftGreyKernel, generatedFourthLiftGreyKernelFast, he, hs]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
