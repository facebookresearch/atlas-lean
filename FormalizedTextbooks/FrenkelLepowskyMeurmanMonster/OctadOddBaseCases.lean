/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual spatial cases in the preferred-Q octad/odd output selector. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddBaseSelector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddPhysicalLabel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddOmegaCases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddIntersection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddPhysicalPair

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- At equal physical indices the actual preferred-Q output occurs exactly
outside the octad, at its normalized restriction character. -/
theorem griessOctadOdd_base_same (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i : Fin 24)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, i)))).base ↔
      i ∉ golayOctadSupport o ∧ e = octadTensorCharacterLabel o f := by
  rw [griessOctadOdd_base_iff_coordinates]
  simp only [hd, true_and]
  rw [octadOddPhysical_syndrome_iff o e (octadOddIntersection o f)
    (octadOddIntersection_supported o f) (octadOddIntersection_even o f)]
  simp only [ne_eq, not_true_eq_false, false_and, true_and, or_false,
    octadOddIntersection_normalize, octadSignLabelEquiv.injective.eq_iff]
  constructor
  · rintro ⟨he,hω⟩
    subst e
    exact ⟨(octadOddOmega_same o d f i hd).mp hω,rfl⟩
  · rintro ⟨hi,he⟩
    subst e
    exact ⟨rfl,(octadOddOmega_same o d f i hd).mpr hi⟩

/-- Two distinct positions with at least one outside the octad have no preferred odd output. -/
theorem griessOctadOdd_base_other_zero (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (i j : Fin 24) (hij : i ≠ j)
    (hout : i ∉ golayOctadSupport o ∨ j ∉ golayOctadSupport o) :
    (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, i)))).base ≠
        (griessShortQ (Sum.inr (Sum.inr (f, j)))).base := by
  intro hb
  have hs := ((griessOctadOdd_base_iff_coordinates o e d f i j).mp hb).2.1
  rw [octadOddPhysical_syndrome_iff o e (octadOddIntersection o f)
    (octadOddIntersection_supported o f) (octadOddIntersection_even o f)] at hs
  rcases hs with ⟨he,_⟩ | ⟨_,hi,hj,_⟩
  · exact hij he
  · rcases hout with h | h
    · exact h hi
    · exact h hj

/-- At two distinct positions inside the octad, the actual preferred-Q output
occurs exactly at the pair-shifted normalized restriction character. -/
theorem griessOctadOdd_base_inside (o : Fin 759) (e : Fin 64)
    (d f : Fin 2048) (a b : Fin 8) (hab : a ≠ b)
    (hd : spinDictionaryCode (octadSpinLow f + octadSpinCode o) = d) :
    (griessShortQ (Sum.inr (Sum.inl (o, e))) *
      griessShortQ (Sum.inr (Sum.inr (d, golayOctadCoordinate o a)))).base =
        (griessShortQ (Sum.inr (Sum.inr (f, golayOctadCoordinate o b)))).base ↔
      e = trialityXor (octadTensorCharacterLabel o f) (trialityOctadPairShift a b) := by
  have hij : golayOctadCoordinate o a ≠ golayOctadCoordinate o b :=
    fun h => hab (golayOctadCoordinate_injective o h)
  have hi : golayOctadCoordinate o a ∈ golayOctadSupport o :=
    (golayOctadWord_ne_zero_iff o _).mp (by rw [golayOctadWord_local]; exact one_ne_zero)
  have hj : golayOctadCoordinate o b ∈ golayOctadSupport o :=
    (golayOctadWord_ne_zero_iff o _).mp (by rw [golayOctadWord_local]; exact one_ne_zero)
  rw [griessOctadOdd_base_iff_coordinates]
  simp only [hd, true_and]
  rw [octadOddPhysical_syndrome_iff o e (octadOddIntersection o f)
    (octadOddIntersection_supported o f) (octadOddIntersection_even o f)]
  simp only [hij, false_and, false_or, hi, hj, true_and]
  rw [octadOddPhysical_normalized_pair_shift o (octadOddIntersection o f)
    (octadTensorCharacterLabel o f) (octadOddIntersection_normalize o f) a b hab]
  simp only [octadSignLabelEquiv.injective.eq_iff]
  constructor
  · exact fun h => h.1.2
  · intro he
    subst e
    exact ⟨⟨hij,rfl⟩,octadOddOmega_inside o d f a b hab hd⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
