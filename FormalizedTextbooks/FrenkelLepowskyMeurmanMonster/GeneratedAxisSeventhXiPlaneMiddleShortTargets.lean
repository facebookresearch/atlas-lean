/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneMiddleShortOctads

/-! Genuine preferred short labels reconstructed from the checked physical shapes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The checked pair descriptor has increasing valid coordinates and its actual sign index. -/
theorem generatedSeventhXiShort_pair_data (s : Fin 2) (p : Fin 276)
    (hk : generatedSeventhXiShortDescriptor s p 0 = 0) :
    generatedSeventhXiShortDescriptor s p 1 < 2 ∧
    generatedSeventhXiShortDescriptor s p 2 < generatedSeventhXiShortDescriptor s p 3 ∧
    generatedSeventhXiShortDescriptor s p 3 < 24 := by
  have h := (generatedSeventhXiShort_shapes s p).2.2
  simpa only [hk, ite_true] using h

/-- The checked odd descriptor retains the genuine low code label and physical coordinate. -/
theorem generatedSeventhXiShort_odd_data (s : Fin 2) (p : Fin 276)
    (h0 : generatedSeventhXiShortDescriptor s p 0 ≠ 0)
    (h1 : generatedSeventhXiShortDescriptor s p 0 ≠ 1) :
    generatedSeventhXiShortDescriptor s p 1 < 2048 ∧
    generatedSeventhXiShortDescriptor s p 2 < 24 := by
  have h := (generatedSeventhXiShort_shapes s p).2.2
  simpa only [ite_eq_right h0, ite_eq_right h1] using h

/-- Actual catalogue labels selected semantically from certified physical descriptors. -/
def generatedSeventhXiShortOutputLabel (s : Fin 2) (p : Fin 276) : GriessShortIndex :=
  if h0 : generatedSeventhXiShortDescriptor s p 0 = 0 then
    let h := generatedSeventhXiShort_pair_data s p h0
    let a : Fin 24 := ⟨generatedSeventhXiShortDescriptor s p 2, by omega⟩
    let b : Fin 24 := ⟨generatedSeventhXiShortDescriptor s p 3, h.2.2⟩
    Sum.inl (⟨generatedSeventhXiShortDescriptor s p 1, h.1⟩,
      griessPairIndex a b (by apply ne_of_lt; exact h.2.1))
  else if h1 : generatedSeventhXiShortDescriptor s p 0 = 1 then
    Sum.inr (Sum.inl (generatedSeventhXiShortOutputOctad s p h1,
      ⟨generatedSeventhXiShortDescriptor s p 2 % 64, Nat.mod_lt _ (by decide)⟩))
  else
    let h := generatedSeventhXiShort_odd_data s p h0 h1
    Sum.inr (Sum.inr (⟨generatedSeventhXiShortDescriptor s p 1, h.1⟩,
      ⟨generatedSeventhXiShortDescriptor s p 2, h.2⟩))

/-- Reconstructed catalogue labels have exactly the certified integer coordinates. -/
theorem generatedSeventhXiShortOutputLabel_integral (s : Fin 2) (p : Fin 276) :
    griessShortIntegral (generatedSeventhXiShortOutputLabel s p) =
      generatedSeventhXiShortOutputIntegral s p := by
  funext i
  by_cases h0 : generatedSeventhXiShortDescriptor s p 0 = 0
  · have hp := generatedSeventhXiShort_pair_data s p h0
    simp only [generatedSeventhXiShortOutputLabel, h0, dite_true,
      generatedSeventhXiShortOutputIntegral, ite_true]
    simp only [griessShortIntegral, griessPairIndex_coordinates, Fin.lt_def,
      hp.2.1, ite_true, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> norm_num
  · by_cases h1 : generatedSeventhXiShortDescriptor s p 0 = 1
    · simp only [generatedSeventhXiShortOutputLabel, h1, Nat.one_ne_zero, dite_false, dite_true,
        generatedSeventhXiShortOutputIntegral, ite_false, ite_true]
      simp only [griessShortIntegral, generatedSeventhXiShortOutputOctad_code,
        generatedSeventhXiShortOutputOctad_sign]
    · simp only [generatedSeventhXiShortOutputLabel, h0, h1, dite_false,
        generatedSeventhXiShortOutputIntegral, ite_false, griessShortIntegral, Fin.ext_iff]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
