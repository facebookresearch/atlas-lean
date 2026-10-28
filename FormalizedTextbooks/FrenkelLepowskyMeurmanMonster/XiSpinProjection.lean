/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The grey projections used in the exact spin normalizer calculation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinGray

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The nonsingular six-dimensional off-diagonal pairing matrix. -/
def xiGrayDual (a : XiGrayIndex) : XiGrayIndex :=
  fun i => ∑ j, a j * (if i = j then 0 else 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The finite function space has 64 vectors to check.
/-- Its inverse is itself, because the dimension is even. -/
theorem xiGrayDual_involutive : Function.Involutive xiGrayDual := by
  change ∀ a : XiGrayIndex, xiGrayDual (xiGrayDual a) = a
  decide +kernel

theorem xiGrayBilinear_dual (a b : XiGrayIndex) :
    xiGrayBilinear a b = ∑ i, a i * xiGrayDual b i := by
  simp [xiGrayBilinear, xiGrayDual, Finset.mul_sum ]

theorem xiSpinDot_sum_left {ι : Type*} [Fintype ι] (a : ι → SpinIndex) (b : SpinIndex) :
    spinDot (∑ i, a i) b = ∑ i, spinDot (a i) b := by
  simp only [spinDot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem xiSpinDot_sum_right {ι : Type*} [Fintype ι] (a : SpinIndex) (b : ι → SpinIndex) :
    spinDot a (∑ i, b i) = ∑ i, spinDot a (b i) := by
  simp only [spinDot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem xiSpinDot_smul_left (c : ZMod 2) (a b : SpinIndex) :
    spinDot (c • a) b = c * spinDot a b := by
  simp [spinDot, Finset.mul_sum, mul_assoc]

theorem xiSpinDot_smul_right (c : ZMod 2) (a b : SpinIndex) :
    spinDot a (c • b) = c * spinDot a b := by
  simp only [spinDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  ext i
  ring

theorem xiGrayCode_dot (a : XiGrayIndex) (b : SpinIndex) :
    spinDot b (xiGrayCode a) = ∑ i, a i * spinDot b (xiGrayCodeBasis i) := by
  change spinDot b (∑ i, a i • xiGrayCodeBasis i) = _
  simp_rw [xiSpinDot_sum_right, xiSpinDot_smul_right]

theorem xiGrayCocode_dot (a : XiGrayIndex) (b : SpinIndex) :
    spinDot (xiGrayCocode a) b = ∑ i, a i * spinDot (xiGrayCocodeBasis i) b := by
  change spinDot (∑ i, a i • xiGrayCocodeBasis i) b = _
  simp_rw [xiSpinDot_sum_left, xiSpinDot_smul_left]

theorem xiGrayCode_cocode_pairing (a b : XiGrayIndex) :
    spinDot (xiGrayCocode a) (xiGrayCode b) = xiGrayBilinear a b := by
  rw [xiGrayCocode_dot]
  simp_rw [xiGrayCode_dot, xiGrayBasis_pairing, Finset.mul_sum]
  simp [xiGrayBilinear ]

/-- Grey code coefficients read from commutation with the six cocode generators. -/
def xiGrayGammaProjection (q : Q) : XiGrayIndex :=
  xiGrayDual (fun i => spinDot (xiGrayCocodeBasis i) (spinTranslation q))

/-- Grey cocode coefficients read from commutation with the six code generators. -/
def xiGrayGProjection (q : Q) : XiGrayIndex :=
  xiGrayDual (fun i => spinDot (spinModulation q) (xiGrayCodeBasis i))

theorem xiGrayGammaProjection_pairing (a : XiGrayIndex) (q : Q) :
    spinDot (xiGrayCocode a) (spinTranslation q) = xiGrayBilinear a (xiGrayGammaProjection q) := by
  rw [xiGrayCocode_dot, xiGrayBilinear_dual]
  simp only [xiGrayGammaProjection]
  rw [xiGrayDual_involutive _]

theorem xiGrayGProjection_pairing (a : XiGrayIndex) (q : Q) :
    spinDot (spinModulation q) (xiGrayCode a) = xiGrayBilinear a (xiGrayGProjection q) := by
  rw [xiGrayCode_dot, xiGrayBilinear_dual]
  simp only [xiGrayGProjection]
  rw [xiGrayDual_involutive _]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
