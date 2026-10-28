/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhysicalSupport

/-! The actual coordinate-octad and actual short-line flag detected by the
fourth matrix. The line sign comes from the genuine full-Q source phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual octad on coordinates four through eleven. -/
noncomputable def generatedFourthFlagOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨(⟨14, by decide⟩ : Fin 4096), by decide +kernel⟩

/-- The genuine finite octad index retains code label fourteen. -/
theorem generatedFourthFlagOctad_label : golayOctadLabel generatedFourthFlagOctad = 14 := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨(⟨14, by decide⟩ : Fin 4096), by decide +kernel⟩)

/-- Its literal coordinate mask is four through eleven. -/
theorem generatedFourthFlagOctad_mask :
    golayEncodedMask (golayOctadLabel generatedFourthFlagOctad).val = 0xff0 := by
  rw [generatedFourthFlagOctad_label]
  decide +kernel

/-- The line sign compensates the actual preferred-Q phase. -/
noncomputable def generatedFourthFlagSign : Fin 2 :=
  if generatedFourthPairPhase = 0 then 0 else 1

/-- The distinguished line is an actual preferred pair-short label. -/
noncomputable def generatedFourthFlagShort : GriessShortIndex :=
  Sum.inl (generatedFourthFlagSign, griessPairIndex 8 11 (by decide))

/-- The distinguished actual short line lies in the distinguished actual E8 section. -/
theorem generatedFourthFlagShort_supported :
    generatedOctadShortSupport generatedFourthFlagOctad generatedFourthFlagShort := by
  rw [generatedOctadShortSupport_iff_physical]
  intro i hi
  rw [generatedFourthFlagOctad_mask] at hi
  have h8 : Nat.testBit 0xff0 8 = true := by decide
  have h11 : Nat.testBit 0xff0 11 = true := by decide
  have hn8 : i ≠ 8 := by
    intro h
    subst i
    change Nat.testBit 0xff0 8 = false at hi
    rw [h8] at hi
    contradiction
  have hn11 : i ≠ 11 := by
    intro h
    subst i
    change Nat.testBit 0xff0 11 = false at hi
    rw [h11] at hi
    contradiction
  simp only [generatedFourthFlagShort, griessShortVector, griessShortIntegral,
    generatedFourthPairInput_coordinates, hn8, hn11, ite_false, mul_zero, zero_add,
    Int.cast_zero, zero_div]

/-- The sorted preferred pair represents either orientation of coordinates eight and eleven. -/
theorem generatedFourth_pair_coordinates_iff (i j : Fin 24) (hij : i ≠ j) :
    griessCoordinatePair (griessPairIndex i j hij) = (8, 11) ↔
      (i = 8 ∧ j = 11) ∨ (i = 11 ∧ j = 8) := by
  rw [griessPairIndex_coordinates]
  by_cases h : i < j
  · rw [ite_eq_left h]
    simp only [Prod.mk.injEq]
    constructor
    · exact Or.inl
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · norm_num at h
  · rw [ite_eq_right h]
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num at h
      · exact ⟨rfl, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
