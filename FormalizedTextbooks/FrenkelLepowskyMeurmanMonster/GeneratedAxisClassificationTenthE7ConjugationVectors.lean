/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7ConjugationCoordinates

/-! Actual lattice vectors and actual Golay octad of the transported seven-pair flag. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The actual Golay word of the transported physical octad. -/
def generatedTenthE7OctadWord : Fin 24 → ZMod 2 :=
  golayEncoder (golayLabelCoefficients ⟨198, by decide⟩)

/-- The transported coordinate support is an actual Golay codeword. -/
theorem generatedTenth_e7_octad_mem_code : generatedTenthE7OctadWord ∈ golayCode :=
  ⟨golayLabelCoefficients ⟨198, by decide⟩, rfl⟩

/-- Its complete actual coordinates equal the specified physical octad support. -/
theorem generatedTenth_e7_octad_coordinates : ∀ i : Fin 24,
    generatedTenthE7OctadWord i =
      if i ∈ generatedTenthE7OctadSupport then 1 else 0 := by
  decide +kernel

/-- The genuine codeword has the actual octad weight eight. -/
theorem generatedTenth_e7_octad_weight :
    ∑ i, (generatedTenthE7OctadWord i).val = 8 := by
  decide +kernel

/-- The integral norm-four pair root perpendicular to the transported E7 hyperplane. -/
def generatedTenthE7NormalVector (i : Fin 24) : ℤ :=
  4 * generatedTenthE7NormalDirection i

/-- The actual norm-twelve vector on the distinguished transported line. -/
def generatedTenthE7DistinguishedVector (i : Fin 24) : ℤ :=
  4 * generatedTenthE7LineDirection i

/-- The perpendicular pair root belongs to the original integral Leech lattice. -/
theorem generatedTenth_e7_normal_mem : generatedTenthE7NormalVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [generatedTenthE7NormalVector, Int.cast_mul, Int.cast_ofNat,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero, add_zero,
      show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ i, generatedTenthE7NormalVector i = 8 := by decide +kernel
    rw [hs]
    change (8 : ZMod 8) = 0
    decide

/-- The distinguished transported vector belongs to the original integral Leech lattice. -/
theorem generatedTenth_e7_distinguished_mem :
    generatedTenthE7DistinguishedVector ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [generatedTenthE7DistinguishedVector, Int.cast_mul, Int.cast_ofNat,
      Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, Int.cast_zero, add_zero,
      show (4 : ZMod 4) = 0 by decide, zero_mul]
  · have hs : ∑ i, generatedTenthE7DistinguishedVector i = 8 := by decide +kernel
    rw [hs]
    change (8 : ZMod 8) = 0
    decide

/-- The actual normalized perpendicular root has norm four. -/
theorem generatedTenth_e7_normal_square :
    leechSquareSum generatedTenthE7NormalVector = 32 := by decide +kernel

/-- The actual normalized distinguished vector has norm twelve. -/
theorem generatedTenth_e7_distinguished_square :
    leechSquareSum generatedTenthE7DistinguishedVector = 96 := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
