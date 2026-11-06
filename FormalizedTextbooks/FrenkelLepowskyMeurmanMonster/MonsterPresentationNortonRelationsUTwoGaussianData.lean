/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine rank-four translation Gaussian for the actual squared Norton spin action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The two omitted grey directions and four actual coordinate translations. -/
def monsterNortonUTwoGaussianBasis : Fin 6 → SpinIndex :=
  ![0, 0, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1]

/-- The rank-four image of the genuine six-dimensional elementary abelian group. -/
def monsterNortonUTwoGaussianCode : XiGrayIndex →ₗ[ZMod 2] SpinIndex where
  toFun a := ∑ i, a i • monsterNortonUTwoGaussianBasis i
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [mul_smul, Finset.smul_sum]

/-- Pure translations with their actual normalized central coefficients. -/
def monsterNortonUTwoGaussianTranslation : Multiplicative XiGrayIndex →* Q where
  toFun a := ⟨ofAdd (Fin.append (monsterNortonUTwoGaussianCode (toAdd a)) (0 : SpinIndex)), 1⟩
  map_one' := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change Fin.append (monsterNortonUTwoGaussianCode 0) (0 : SpinIndex) = 0
      rw [map_zero]
      ext i
      refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply]
    · rfl
  map_mul' a b := by
    apply NormalizedCocycleExtension.Extension.ext
    · apply toAdd.injective
      change Fin.append (monsterNortonUTwoGaussianCode (toAdd a + toAdd b)) (0 : SpinIndex) =
        Fin.append (monsterNortonUTwoGaussianCode (toAdd a)) (0 : SpinIndex) +
          Fin.append (monsterNortonUTwoGaussianCode (toAdd b)) (0 : SpinIndex)
      rw [map_add]
      ext i
      refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.append_left, Fin.append_right, Pi.zero_apply,
          Pi.add_apply, add_zero]
    · apply toAdd.injective
      change 0 = 0 + 0 + qBeta
        (Fin.append (monsterNortonUTwoGaussianCode (toAdd a)) (0 : SpinIndex))
        (Fin.append (monsterNortonUTwoGaussianCode (toAdd b)) (0 : SpinIndex))
      simp only [qBeta, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_add]


/-- Read the six commutation coefficients using the nonsingular grey pairing. -/
def monsterNortonUTwoGaussianProjection (q : Q) : XiGrayIndex :=
  xiGrayDual (fun i => spinDot (spinModulation q) (monsterNortonUTwoGaussianBasis i))

/-- Projection exactly recovers commutation with the represented translations. -/
theorem monsterNortonUTwoGaussianProjection_pairing (a : XiGrayIndex) (q : Q) :
    spinDot (spinModulation q) (monsterNortonUTwoGaussianCode a) =
      xiGrayBilinear a (monsterNortonUTwoGaussianProjection q) := by
  change spinDot (spinModulation q) (∑ i, a i • monsterNortonUTwoGaussianBasis i) = _
  simp_rw [xiSpinDot_sum_right, xiSpinDot_smul_right]
  rw [xiGrayBilinear_dual]
  simp only [monsterNortonUTwoGaussianProjection]
  rw [xiGrayDual_involutive _]

/-- The actual operator, obtained by specializing the proved grey Gaussian. -/
noncomputable def monsterNortonUTwoGaussian : SpinSpace →ₗ[ℝ] SpinSpace :=
  xiGrayGaussian (spinLinearRepresentation.comp monsterNortonUTwoGaussianTranslation)

/-- The specialized operator remains an actual involution. -/
theorem monsterNortonUTwoGaussian_square :
    monsterNortonUTwoGaussian * monsterNortonUTwoGaussian = 1 :=
  xiGrayGaussian_square _

set_option maxRecDepth 4096 in
/-- The actual rank-four operator preserves the real spin pairing. -/
theorem monsterNortonUTwoGaussian_pairing (f h : SpinSpace) :
    spinPairing (monsterNortonUTwoGaussian f) (monsterNortonUTwoGaussian h) =
      spinPairing f h := xiGrayGaussian_spin_pairing _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
