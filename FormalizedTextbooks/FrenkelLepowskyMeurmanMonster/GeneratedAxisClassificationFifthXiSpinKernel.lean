/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! An exact integral coordinate kernel for the actual three-bases spin operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual Pauli correction to be checked against every original fifth-axis block. -/
def generatedFifthXiCorrection : Q :=
  generatedAxisFourthQFromSpin (golayLabelCoefficients 11) (golayLabelCoefficients 15) 1

/-- Eight times the actual Gaussian spin matrix entry at two original coordinate units. -/
def generatedFifthXiSpinKernel (t v : SpinIndex) : ℤ :=
  ∑ a : XiGrayIndex, if t + xiGrayCode a = v then
    xiGraySign a * nortonUIntegerGammaSign v else 0

/-- The integer kernel embeds as the genuine actual Xi spin action on a coordinate unit. -/
theorem generatedFifth_xi_spin_unit (v t : SpinIndex) :
    xiSpinHolomorph.val (Pi.single v 1 : SpinSpace) t =
      (generatedFifthXiSpinKernel t v : ℝ) / 8 := by
  change xiSpinG (xiSpinGamma (Pi.single v 1)) t = _
  rw [nortonUIntegerG_apply]
  simp_rw [nortonUIntegerGamma_apply]
  simp only [generatedFifthXiSpinKernel, Int.cast_sum, Int.cast_ite, Int.cast_mul,
    Int.cast_zero, xiGraySign_real, Pi.single_apply, div_eq_mul_inv,
    Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : t + xiGrayCode a = v
  · simp only [h, ite_true, mul_one]
    ring
  · simp only [h, ite_false, mul_zero, zero_mul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
