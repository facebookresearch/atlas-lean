/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneSpinCertificates

/-! The finite integer state is the explicit normalized form of the genuine middle spin state. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Each source label has its exactly certified normalized real coefficient. -/
theorem generatedSeventhXiPlaneSpinInteger_coordinate (d : Fin 4096) :
    generatedSeventhXiPlaneNormalizedSpin (golayLabelCoefficients d) =
      (generatedSeventhXiPlaneSpinInteger d : ℝ) / 16 := by
  let b : Fin 64 := ⟨d.val / 64, by omega⟩
  let i : Fin 64 := ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩
  have hd : (⟨64 * b.val + i.val, by omega⟩ : Fin 4096) = d := by
    apply Fin.ext
    dsimp only [b, i]
    omega
  have hc := generatedSeventhXiPlaneSpin_cache b i
  dsimp only at hc
  rw [hd] at hc
  by_cases ht : generatedSeventhSpinSupportMatrix *ᵥ golayLabelCoefficients d = 0
  · have hs := hc.1.mpr ht
    have hp := hc.2 ht
    simp only [generatedSeventhXiPlaneNormalizedSpin, ht, ite_true, hp]
    change qSign (golayBooleanCast
      ((generatedSeventhXiPlaneSpinNegativeRows b).testBit i.val)) / 16 = _
    simp only [generatedSeventhXiPlaneSpinInteger]
    change _ = ((if (generatedSeventhXiPlaneSpinSupportRows b).testBit i.val then
      if (generatedSeventhXiPlaneSpinNegativeRows b).testBit i.val then (-1 : ℤ) else 1
      else 0 : ℤ) : ℝ) / 16
    rw [hs]
    cases hn : (generatedSeventhXiPlaneSpinNegativeRows b).testBit i.val <;>
      simp [golayBooleanCast, qSign]
  · have hs : (generatedSeventhXiPlaneSpinSupportRows b).testBit i.val = false := by
      cases hs : (generatedSeventhXiPlaneSpinSupportRows b).testBit i.val
      · rfl
      · exact False.elim (ht (hc.1.mp hs))
    simp only [generatedSeventhXiPlaneNormalizedSpin, ht, ite_false]
    simp only [generatedSeventhXiPlaneSpinInteger]
    change (0 : ℝ) = ((if (generatedSeventhXiPlaneSpinSupportRows b).testBit i.val then
      if (generatedSeventhXiPlaneSpinNegativeRows b).testBit i.val then (-1 : ℤ) else 1
      else 0 : ℤ) : ℝ) / 16
    rw [hs]
    norm_num

/-- The original middle state is one of the two signs of this fully checked integer embedding. -/
theorem generatedSeventhXiPlaneSpinInteger_original_sign :
    generatedSeventhSpinState = (1 / 16 : ℝ) •
      nortonUIntegerEmbed generatedSeventhXiPlaneSpinInteger ∨
    generatedSeventhSpinState = -(1 / 16 : ℝ) •
      nortonUIntegerEmbed generatedSeventhXiPlaneSpinInteger := by
  have he : generatedSeventhXiPlaneNormalizedSpin =
      (1 / 16 : ℝ) • nortonUIntegerEmbed generatedSeventhXiPlaneSpinInteger := by
    funext t
    have h := generatedSeventhXiPlaneSpinInteger_coordinate (nortonUIntegerLabel t)
    rw [nortonUIntegerLabel_inverse] at h
    simpa only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed, div_eq_mul_inv,
      one_mul, mul_comm] using h
  rcases generatedSeventhXiPlane_spin_normalized_sign with h | h
  · exact Or.inl (h.trans he)
  · right
    rw [h, he, neg_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
