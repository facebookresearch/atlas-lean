/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorOperators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified

/-! A bounded exact Gaussian formula for all rational tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- All 64 original spin inputs and four original spatial inputs, with a certified zero guard. -/
def generatedAxisGlobalRationalTensorXiCached (T : GeneratedAxisGlobalRationalTensor)
    (k : Fin 4096) (i : Fin 24) : ℚ :=
  (∑ a : Fin 64, ∑ b : Fin 4,
    let m := generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)
    let j := generatedAxisGlobalXiColumn i b
    let z := T m j
    if z = 0 then 0 else
      (generatedSixthGraySign a : ℚ) * (generatedSixthSpinGammaFast m : ℚ) *
        (co1XiNumerator i j : ℚ) * z) / 16

private theorem rationalXi_phase (a : XiGrayIndex) (t : SpinIndex) :
    generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a t) =
      xiGraySign a * nortonUIntegerGammaSign (t + xiGrayCode a) := by
  have h : ∀ p q : ZMod 2, generatedAxisGlobalIntSign (p + q + 1) =
      generatedAxisGlobalIntSign p * (-generatedAxisGlobalIntSign q) := by decide +kernel
  exact h (xiGrayQuadratic a)
    (xiGrayQuadratic (generatedAxisGlobalXiGammaIndex (t + xiGrayCode a)))

/-- The fast finite expression equals the full original rational Gaussian at every coordinate. -/
theorem generatedAxisGlobalRationalTensorXiCached_eq
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalRationalTensorXiCached T = generatedAxisGlobalRationalTensorXi T := by
  funext k i
  unfold generatedAxisGlobalRationalTensorXiCached generatedAxisGlobalRationalTensorXi
  apply congrArg (fun z : ℚ => z / 16)
  rw [← Equiv.sum_comp generatedSixthGrayEquiv]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hc : xiGrayCode (generatedSixthGrayCoefficients a) =
      golayLabelCoefficients (generatedSixthGrayCodeLabel a) :=
    (funext (generatedSixth_gray_code a)).symm
  change (let m := generatedSixthSpinLabelXor k (generatedSixthGrayCodeLabel a)
          let z := T m (generatedAxisGlobalXiColumn i b)
          if z = 0 then 0 else _) =
    (generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase
      (generatedSixthGrayCoefficients a) (golayLabelCoefficients k)) : ℚ) *
      (co1XiNumerator i (generatedAxisGlobalXiColumn i b) : ℚ) *
      T (generatedAxisGlobalSpinLabel (golayLabelCoefficients k +
        xiGrayCode (generatedSixthGrayCoefficients a))) (generatedAxisGlobalXiColumn i b)
  rw [rationalXi_phase, hc, ← generatedSixth_spin_label_xor,
    generatedAxisGlobalSpinLabel_coeff]
  dsimp only
  rw [← generatedSixth_gray_sign, ← generatedSixth_spin_gamma_fast]
  split_ifs with hz
  · simp only [hz, mul_zero]
  · push_cast
    ring

/-- Every fast rational coordinate is still the complete genuine real Xi operator. -/
theorem generatedAxisGlobalRationalTensorXiCached_actual
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation xiSpinLocalFiber (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalRationalTensorXiCached T) := by
  rw [generatedAxisGlobalRationalTensorXiCached_eq]
  exact generatedAxisGlobalRationalTensorXi_actual T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
