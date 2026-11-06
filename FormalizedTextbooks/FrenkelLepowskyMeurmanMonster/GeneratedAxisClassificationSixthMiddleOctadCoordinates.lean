/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOctadPhysical6

/-! The displayed physical octad images are genuine preferred-short permutation labels. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every displayed octad target equals the original physical frame-column image. -/
theorem generatedSixth_middle_octad_physical_certificate (k : Fin 273) (i : Fin 24) :
    generatedSixthFrameVectorData 8 (generatedSixthMiddleOctadSourceCoordinates k).2.1 i +
      (if (generatedSixthMiddleOctadSourceCoordinates k).1 = 0 then -1 else 1) *
        generatedSixthFrameVectorData 8 (generatedSixthMiddleOctadSourceCoordinates k).2.2 i =
      2 * generatedSixthMiddleOctadPhysicalSign k *
        griessShortIntegral (generatedSixthMiddleOctadOutput k) i := by
  simp only [generatedSixthMiddleOctadOutput_integral]
  by_cases hk0 : k.val < 39
  · have hj : k.val - 0 < 39 := by omega
    have hn : (⟨0 + (k.val - 0), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 0 + (k.val - 0) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate0
      (⟨k.val - 0, hj⟩ : Fin 39) i
  by_cases hk1 : k.val < 78
  · have hj : k.val - 39 < 39 := by omega
    have hn : (⟨39 + (k.val - 39), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 39 + (k.val - 39) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate1
      (⟨k.val - 39, hj⟩ : Fin 39) i
  by_cases hk2 : k.val < 117
  · have hj : k.val - 78 < 39 := by omega
    have hn : (⟨78 + (k.val - 78), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 78 + (k.val - 78) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate2
      (⟨k.val - 78, hj⟩ : Fin 39) i
  by_cases hk3 : k.val < 156
  · have hj : k.val - 117 < 39 := by omega
    have hn : (⟨117 + (k.val - 117), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 117 + (k.val - 117) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate3
      (⟨k.val - 117, hj⟩ : Fin 39) i
  by_cases hk4 : k.val < 195
  · have hj : k.val - 156 < 39 := by omega
    have hn : (⟨156 + (k.val - 156), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 156 + (k.val - 156) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate4
      (⟨k.val - 156, hj⟩ : Fin 39) i
  by_cases hk5 : k.val < 234
  · have hj : k.val - 195 < 39 := by omega
    have hn : (⟨195 + (k.val - 195), by omega⟩ : Fin 273) = k := by
      apply Fin.ext
      change 195 + (k.val - 195) = k.val
      omega
    simpa only [hn] using generatedSixth_middle_octad_physical_certificate5
      (⟨k.val - 195, hj⟩ : Fin 39) i
  have hj : k.val - 234 < 39 := by omega
  have hn : (⟨234 + (k.val - 234), by omega⟩ : Fin 273) = k := by
    apply Fin.ext
    change 234 + (k.val - 234) = k.val
    omega
  simpa only [hn] using generatedSixth_middle_octad_physical_certificate6
    (⟨k.val - 234, hj⟩ : Fin 39) i

/-- The genuine original lattice action realizes the target with its physical vector sign. -/
theorem generatedSixth_middle_octad_integral_image (k : Fin 273) :
    (leechIntegralAction generatedSixthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOctadInput k)))).val =
      fun i => generatedSixthMiddleOctadPhysicalSign k *
        griessShortIntegral (generatedSixthMiddleOctadOutput k) i := by
  funext i
  have hf := generatedSixth_forward_pair_coordinate
    (generatedSixthMiddleOctadInput k).1 (generatedSixthMiddleOctadInput k).2 i
  unfold generatedSixthMiddleOctadInput at hf
  rw [griessPairIndex_coordinates,
    ite_eq_left (generatedSixth_middle_octad_source_lt k)] at hf
  have hc := generatedSixth_middle_octad_physical_certificate k i
  rw [hc] at hf
  change 2 * (leechIntegralAction generatedSixthLocalFiber.val.2
    (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOctadInput k)))).val i =
      2 * generatedSixthMiddleOctadPhysicalSign k *
        griessShortIntegral (generatedSixthMiddleOctadOutput k) i at hf
  apply mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0)
  simpa only [mul_assoc] using hf

/-- Every displayed octad target is the genuine original preferred-short image. -/
theorem generatedSixth_middle_octad_permutation (k : Fin 273) :
    generatedSixthMiddleShortLabel (generatedSixthMiddleOctadInput k) =
      generatedSixthMiddleOctadOutput k := by
  apply generatedSixth_short_label_of_integral_image
  have h := generatedSixth_middle_octad_integral_image k
  rcases generatedSixth_middle_octad_physical_sign k with hs | hs
  · left
    simpa only [hs, one_mul] using h
  · right
    change (leechIntegralAction generatedSixthLocalFiber.val.2
      (griessShortLatticeVector (Sum.inl (generatedSixthMiddleOctadInput k)))).val =
        fun i => -griessShortIntegral (generatedSixthMiddleOctadOutput k) i
    simpa only [hs, neg_one_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
