/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthSpinGammaCertified

/-! The original source spin numerator is exactly its already certified finite Gaussian cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Both original binary-address implementations decode exactly the same actual spin labels. -/
theorem generatedTwelfth_tensor_spin_label_norton (t : SpinIndex) :
    nortonUIntegerLabel t = generatedAxisGlobalSpinLabel t := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [nortonUIntegerLabel_coeff, generatedAxisGlobalSpinLabel_coeff]

/-- The complete original spin Xi sum equals the genuine integral Norton Gaussian. -/
theorem generatedTwelfth_tensor_xi_integer_norton (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddXiSpinInteger u = nortonUIntegerXi u := by
  funext k
  apply Int.cast_injective (α := ℝ)
  have ho := generatedAxisGlobalXiSpin_apply (nortonUIntegerEmbed u) (golayLabelCoefficients k)
  have hreal : (generatedAxisGlobalOddXiSpinInteger u k : ℝ) =
      8 * xiSpinOperator (nortonUIntegerEmbed u) (golayLabelCoefficients k) := by
    rw [ho]
    simp only [generatedAxisGlobalOddXiSpinInteger, Int.cast_sum, Int.cast_mul,
      generatedAxisGlobalIntSign_real, nortonUIntegerEmbed,
      generatedTwelfth_tensor_spin_label_norton]
  have hn := congrFun (nortonUIntegerXi_embed u) (golayLabelCoefficients k)
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, nortonUIntegerLabel_coeff] at hn
  rw [generatedAxisGlobalXi_spin_factor] at hn
  rw [hreal, hn]
  ring

/-- The whole original source Xi factor has precisely the already certified fast finite formula. -/
theorem generatedTwelfth_tensor_xi_integer_cached (u : Fin 4096 → ℤ) :
    generatedAxisGlobalOddXiSpinInteger u = generatedSixthIntegerXiCached u := by
  rw [generatedTwelfth_tensor_xi_integer_norton, generatedSixth_integer_xi_cached]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
