/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBlockCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData

/-! Exact source rows of the complete original tensor boundary labels and signs. -/
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The whole original pre label uses precisely its complete fixed source row. -/
theorem generatedNinth_lower_spin_tensor_pre_label_block
    (g : Fin 11) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorPreLabel g (generatedNinthLowerSpinTensorBlockIndex b u) =
      ⟨(generatedNinthLowerSpinTensorPreLabelWords g b ⟨u.val / 16, by omega⟩ /
        2 ^ (12 * (u.val % 16))) % 4096, Nat.mod_lt _ (by decide)⟩ := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hw : (b.val * 256 + u.val) / 16 % 16 = u.val / 16 := by omega
  have hs : (b.val * 256 + u.val) % 16 = u.val % 16 := by omega
  apply Fin.ext
  dsimp only [generatedNinthLowerSpinTensorPreLabel, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hw, hs]

/-- The full original pre sign uses all256original bits in its fixed source row. -/
theorem generatedNinth_lower_spin_tensor_pre_sign_block
    (g : Fin 11) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorPreSign g (generatedNinthLowerSpinTensorBlockIndex b u) =
      if (generatedNinthLowerSpinTensorPreSignWords g b).testBit u.val then (-1 : ℤ) else 1 := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hu : (b.val * 256 + u.val) % 256 = u.val := by omega
  dsimp only [generatedNinthLowerSpinTensorPreSign, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hu]

/-- The whole original post label uses precisely its complete fixed source row. -/
theorem generatedNinth_lower_spin_tensor_post_label_block
    (g : Fin 11) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorPostLabel g (generatedNinthLowerSpinTensorBlockIndex b u) =
      ⟨(generatedNinthLowerSpinTensorPostLabelWords g b ⟨u.val / 16, by omega⟩ /
        2 ^ (12 * (u.val % 16))) % 4096, Nat.mod_lt _ (by decide)⟩ := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hw : (b.val * 256 + u.val) / 16 % 16 = u.val / 16 := by omega
  have hs : (b.val * 256 + u.val) % 16 = u.val % 16 := by omega
  apply Fin.ext
  dsimp only [generatedNinthLowerSpinTensorPostLabel, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hw, hs]

/-- The full original post sign uses all256original bits in its fixed source row. -/
theorem generatedNinth_lower_spin_tensor_post_sign_block
    (g : Fin 11) (b : Fin 16) (u : Fin 256) :
    generatedNinthLowerSpinTensorPostSign g (generatedNinthLowerSpinTensorBlockIndex b u) =
      if (generatedNinthLowerSpinTensorPostSignWords g b).testBit u.val then (-1 : ℤ) else 1 := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hu : (b.val * 256 + u.val) % 256 = u.val := by omega
  dsimp only [generatedNinthLowerSpinTensorPostSign, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
