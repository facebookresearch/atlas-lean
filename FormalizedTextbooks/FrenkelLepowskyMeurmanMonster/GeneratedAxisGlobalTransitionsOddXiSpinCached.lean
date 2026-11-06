/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified

/-! Bind the original odd-family Gaussian numerator to the certified complete physical cache. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem oddXi_integer_label (t : SpinIndex) :
    nortonUIntegerLabel t = generatedAxisGlobalSpinLabel t := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [nortonUIntegerLabel_coeff, generatedAxisGlobalSpinLabel_coeff]

private theorem oddXi_integer_phase (a : XiGrayIndex) (t : SpinIndex) :
    generatedAxisGlobalIntSign (generatedAxisGlobalXiSpinPhase a t) =
      xiGraySign a * nortonUIntegerGammaSign (t + xiGrayCode a) := by
  have h : ∀ p q : ZMod 2, generatedAxisGlobalIntSign (p + q + 1) =
      generatedAxisGlobalIntSign p * (-generatedAxisGlobalIntSign q) := by decide +kernel
  exact h (xiGrayQuadratic a)
    (xiGrayQuadratic (generatedAxisGlobalXiGammaIndex (t + xiGrayCode a)))

/-- The entire original source numerator is the previously certified integer Gaussian. -/
theorem generatedAxisGlobalOddXiSpinInteger_eq_actual (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddXiSpinInteger u = nortonUIntegerXi u := by
  funext k
  simp only [generatedAxisGlobalOddXiSpinInteger, nortonUIntegerXi,
    nortonUIntegerG, nortonUIntegerGamma]
  apply Finset.sum_congr rfl
  intro a _
  rw [oddXi_integer_phase, oddXi_integer_label,
    generatedAxisGlobalSpinLabel_decode]
  ring

/-- Every cached coordinate is the complete genuine original 64-term spin numerator. -/
theorem generatedAxisGlobalOddXiSpinInteger_eq_cached (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddXiSpinInteger u = generatedSixthIntegerXiCached u := by
  rw [generatedAxisGlobalOddXiSpinInteger_eq_actual, generatedSixth_integer_xi_cached]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
