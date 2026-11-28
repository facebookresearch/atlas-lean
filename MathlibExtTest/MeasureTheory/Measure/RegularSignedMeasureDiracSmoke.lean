/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Measure.RegularSignedMeasure

/-!
# Negative Dirac integration on a one-point space

On the compact discrete space Unit, the Dirac signed measure has regular
variation. Multiplication by the real scalar -1 and negation both give
integral -1 when the continuous function is constantly one.
-/

noncomputable section

open MeasureTheory
open MathlibExt.MeasureTheory
open MathlibExt.MeasureTheory.RegularSignedMeasure

namespace MathlibExtTest.RegularSignedMeasureDirac

private def diracSigned : RegularSignedMeasure Unit := by
  refine ⟨(Measure.dirac ()).toSignedMeasure, ?_⟩
  change ((Measure.dirac ()).toSignedMeasure).totalVariation.Regular
  exact (SignedMeasure.totalVariation_regular_iff_hasRegularVariation _).2
    (SignedMeasure.hasRegularVariation_toSignedMeasure (Measure.dirac ()))

private def oneFunction : C(Unit, ℝ) := ContinuousMap.const Unit 1

private theorem dirac_value : signedIntegralDual diracSigned oneFunction = 1 := by
  rw [signedIntegralDual_apply]
  change (∫ᵛ _x : Unit, (1 : ℝ) ∂<•(Measure.dirac ()).toSignedMeasure) = 1
  rw [VectorMeasure.integral_toSignedMeasure]
  simp

example : VectorMeasure.HasRegularVariation (-(diracSigned : SignedMeasure Unit)) :=
  (hasRegularVariation diracSigned).neg

example : signedIntegralDual ((-1 : ℝ) • diracSigned) oneFunction = -1 := by
  rw [signedIntegralDual_smul]
  simp only [_root_.smul_apply, smul_eq_mul, dirac_value, mul_one]

example : regularSignedMeasureIntegral (-diracSigned) oneFunction = -1 := by
  rw [regularSignedMeasureIntegral_apply,
    ← signedIntegralDual_apply (-diracSigned) oneFunction, signedIntegralDual_neg]
  simp only [_root_.neg_apply, dirac_value]

end MathlibExtTest.RegularSignedMeasureDirac
