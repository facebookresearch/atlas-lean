/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorCircuitReplay
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCacheActual

/-! The actual full source spin action retains its exact original square-root normalization. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem label_equal (t : SpinIndex) :
    nortonUIntegerLabel t = generatedAxisGlobalSpinLabel t := by
  obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.surjective t
  rw [nortonUIntegerLabel_coeff, generatedAxisGlobalSpinLabel_coeff]

/-- The full actual source vector is the entire signed cache divided by the genuine square root. -/
theorem generatedRootEight_incoming_tensor_source_embed (r : Fin 8) :
    generatedRootEightIncomingTensorSourceSpin r =
      (1 / Real.sqrt 2 : ℝ) • nortonUIntegerEmbed
        (generatedRootEightIncomingTensorSourceCache r) := by
  ext t
  rw [generatedRootEight_incoming_tensor_source_spin_cache]
  simp only [nortonUIntegerEmbed, Pi.smul_apply, smul_eq_mul, label_equal]
  ring

/-- A complete integer circuit certificate gives every actual incoming real spin coefficient. -/
theorem generatedRootEight_incoming_tensor_spin_normalization (r : Fin 8)
    (h : (generatedRootEightIncomingCompactSpin 0).val
      ((16 : ℝ) • nortonUIntegerEmbed (generatedRootEightIncomingTensorSourceCache r)) =
        nortonUIntegerEmbed (generatedRootEightIncomingTensorSpinInteger r)) (t : SpinIndex) :
    generatedRootEightIncomingTensorSpin r t =
      (generatedRootEightIncomingTensorSpinInteger r (nortonUIntegerLabel t) : ℝ) /
        (16 * Real.sqrt 2) := by
  have ht := congrFun h t
  rw [map_smul] at ht
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed] at ht
  unfold generatedRootEightIncomingTensorSpin
  rw [generatedRootEight_incoming_tensor_source_embed, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hv : (generatedRootEightIncomingCompactSpin 0).val
      (nortonUIntegerEmbed (generatedRootEightIncomingTensorSourceCache r)) t =
        (generatedRootEightIncomingTensorSpinInteger r (nortonUIntegerLabel t) : ℝ) / 16 := by
    linarith
  rw [hv]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
