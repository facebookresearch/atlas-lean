/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationY82Spin

/-! Exact denominator-cleared coordinates of the genuine y82 spin operator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original signed affine address in the y82 plus/minus coordinates. -/
def generatedFourthLiftYAddress (t : SpinIndex) : SpinIndex :=
  t + (1 + t 11) • monsterSourceY82Code

/-- The complete original quadratic phase of this actual signed affine address. -/
def generatedFourthLiftYPhase (t : SpinIndex) : ZMod 2 :=
  spinDot (sourceCodeThetaPolynomial t) monsterSourceY82Code +
    t 11 * spinDot (sourceCodeThetaPolynomial monsterSourceY82Code) t

/-- The exact four-term numerator of the two actual Fourier changes. -/
noncomputable def generatedFourthLiftYNumerator (f : SpinSpace) (t : SpinIndex) : ℝ :=
  qSign (t 11) * qSign (generatedFourthLiftYPhase t) *
    (qSign ((generatedFourthLiftYAddress t) 11) * f (generatedFourthLiftYAddress t) +
      f (monsterSpinOmegaFlip (generatedFourthLiftYAddress t))) +
    qSign (generatedFourthLiftYPhase (monsterSpinOmegaFlip t)) *
    (qSign ((generatedFourthLiftYAddress (monsterSpinOmegaFlip t)) 11) *
      f (generatedFourthLiftYAddress (monsterSpinOmegaFlip t)) +
      f (monsterSpinOmegaFlip (generatedFourthLiftYAddress (monsterSpinOmegaFlip t))))

/-- The actual y82 operator is exactly half its original four-term numerator. -/
theorem generatedFourth_lift_y_numerator (f : SpinSpace) (t : SpinIndex) :
    monsterSourceY82Spin.val f t = generatedFourthLiftYNumerator f t / 2 := by
  change monsterSpinHadamard
    (monsterSourceY82PlusMinus.val (monsterSpinHadamard f)) t = _
  rw [monsterSpinHadamard_apply, monsterSourceY82PlusMinus_apply,
    monsterSourceY82PlusMinus_apply, monsterSpinHadamard_apply, monsterSpinHadamard_apply]
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold generatedFourthLiftYNumerator generatedFourthLiftYPhase generatedFourthLiftYAddress
  field_simp [hs]
  rw [hh]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
