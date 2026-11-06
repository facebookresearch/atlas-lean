/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadPointwiseCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionTransportData

/-! A genuine Golay automorphism transports the standard octad to the recovered support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Five distinct original physical coordinates of the recovered coordinate octad. -/
def generatedNinthSectionFirstFive : Fin 5 → Fin 24 := ![0, 1, 4, 5, 8]

/-- The specified tuple consists of five distinct physical coordinates. -/
theorem generatedNinth_section_first_five_injective :
    Function.Injective generatedNinthSectionFirstFive := by
  decide +kernel

/-- Actual five-transitivity provides a code-preserving transport of this ordered tuple. -/
theorem generatedNinth_section_permutation_exists :
    ∃ p : golayAutomorphismSubgroup, ∀ j : Fin 5,
      p.val (Fin.castAdd 19 j) = generatedNinthSectionFirstFive j :=
  golayAutomorphism_maps_firstFive _ generatedNinth_section_first_five_injective

/-- A chosen actual Golay automorphism transporting the five original coordinates. -/
def generatedNinthOctadPermutation : golayAutomorphismSubgroup :=
  Classical.choose generatedNinth_section_permutation_exists

/-- The actual chosen code automorphism has precisely the specified tuple action. -/
theorem generatedNinth_octad_permutation_first_five (j : Fin 5) :
    generatedNinthOctadPermutation.val (Fin.castAdd 19 j) = generatedNinthSectionFirstFive j :=
  Classical.choose_spec generatedNinth_section_permutation_exists j

/-- Each specified coordinate belongs to the actual recovered octad word. -/
theorem generatedNinth_section_first_five_word : ∀ j : Fin 5,
    golayEncoder (golayLabelCoefficients generatedNinthSectionCode)
      (generatedNinthSectionFirstFive j) = 1 := by
  decide +kernel

/-- Octad uniqueness forces the entire actual recovered word to pull back to the standard word. -/
theorem generatedNinth_octad_permutation_word :
    golayPermute generatedNinthOctadPermutation.val⁻¹
      (golayEncoder (golayLabelCoefficients generatedNinthSectionCode)) =
        golayStandardOctad := by
  apply golayOctad_unique_through_first_five _ _
  · exact ((generatedNinthOctadPermutation⁻¹).property _).mp ⟨_, rfl⟩
  · exact golayStandardOctad_mem
  · change (∑ i : Fin 24,
      (golayEncoder (golayLabelCoefficients generatedNinthSectionCode)
        (generatedNinthOctadPermutation.val i)).val) = 8
    calc
      _ = ∑ i : Fin 24,
          (golayEncoder (golayLabelCoefficients generatedNinthSectionCode) i).val :=
        Equiv.sum_comp generatedNinthOctadPermutation.val
          (fun i => (golayEncoder (golayLabelCoefficients generatedNinthSectionCode) i).val)
      _ = 8 := by
        rw [← golayLabel_weight]
        exact (Finset.mem_filter.mp generatedNinth_section_code_mem).2
  · exact golayStandardOctad_weight
  · intro i hi
    let j : Fin 5 := ⟨i.val, hi⟩
    have hj : Fin.castAdd 19 j = i := Fin.ext rfl
    constructor
    · change golayEncoder (golayLabelCoefficients generatedNinthSectionCode)
        (generatedNinthOctadPermutation.val i) = 1
      rw [← hj, generatedNinth_octad_permutation_first_five]
      exact generatedNinth_section_first_five_word j
    · simp only [golayStandardOctad, show i.val < 8 by omega, ite_true]

/-- The actual tuple transport carries the entire eight-coordinate support. -/
theorem generatedNinth_octad_permutation_support (i : Fin 24) :
    (golayEncodedMask generatedNinthSectionCode.val).testBit
      (generatedNinthOctadPermutation.val i).val = true ↔ i.val < 8 := by
  have h := congrFun generatedNinth_octad_permutation_word i
  have hv := congrArg ZMod.val h
  change (golayEncoder (golayLabelCoefficients generatedNinthSectionCode)
    (generatedNinthOctadPermutation.val i)).val = (golayStandardOctad i).val at hv
  rw [golayLabelEncoder_match] at hv
  by_cases hi : i.val < 8
  · simp only [golayStandardOctad, hi, ite_true] at hv
    have h1 : (1 : ZMod 2).val = 1 := by decide
    rw [h1] at hv
    simpa only [hi, iff_true] using (by
      cases hb : (golayEncodedMask generatedNinthSectionCode.val).testBit
        (generatedNinthOctadPermutation.val i).val <;> simp_all :
          (golayEncodedMask generatedNinthSectionCode.val).testBit
            (generatedNinthOctadPermutation.val i).val = true)
  · simp only [golayStandardOctad, hi, ite_false, ZMod.val_zero] at hv
    simp only [hi, iff_false]
    intro hb
    rw [hb] at hv
    norm_num at hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
